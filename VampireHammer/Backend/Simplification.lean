import VampireHammer.Backend.Common
import VampireHammer.Backend_Preprocessing

/-!
Single-parent structural and simplification rules that need no certificate:
`reorient_equations`, `closure`, `true_and_false_elimination` and
`consistent_polarity_flipping`.

Each handler proves the displayed conclusion as an ordinary formula. A stored
clause parent is first converted back to its parser formula; in the clause
phase the main backend converts the result to clause form again.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Internal

/-- The proof of the only parent at its parser formula, for a derived node. -/
private def singleFormulaParent? (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  if parent.clauseForm then
    fromClauseForm parent.proof parent.target parent.binders.size parent.clauseLiterals?
  else
    pure (some parent.proof)

/-- Reconstruct `reorient_equations`: the conclusion is the parent with some
equations printed with their sides swapped. -/
def reorientEquations (input : RuleInput) : MetaM (Option Expr) := do
  let some parentProof ← singleFormulaParent? input | return none
  BackendPreprocessing.symmMatch parentProof input.target

/-- Reconstruct `closure`, which universally closes a formula's free
variables. Vampire prints the parent already closed, possibly quantifying the
variables in another order, so the parent's universals are instantiated by
unification with the target's. -/
def closure (input : RuleInput) : MetaM (Option Expr) := do
  let some parentProof ← singleFormulaParent? input | return none
  let binderCount := input.step.binders.size
  let some parent := input.parents[0]? | return none
  -- The printed parent quantifies exactly the free variables of the body.
  unless parent.binders.size == binderCount do return none
  let target ← instantiateMVars input.target
  let proof? ← forallBoundedTelescope target (some binderCount) fun variables body => do
    unless variables.size == binderCount do return none
    let arguments? ← withNewMCtxDepth do
      let (arguments, _, parentBody) ←
        forallMetaBoundedTelescope (← inferType parentProof) binderCount
      unless arguments.size == binderCount do return none
      unless ← isDefEq parentBody body do return none
      let arguments ← arguments.mapM instantiateMVars
      if arguments.any (·.hasExprMVar) then return none
      pure (some arguments)
    let some arguments := arguments? | return none
    some <$> mkLambdaFVars variables (mkAppN parentProof arguments)
  let some proof := proof? | return none
  asExpectedType proof input.target

/-- Reconstruct `true_and_false_elimination` (Vampire's `SimplifyFalseTrue`).
Both the parent and the conclusion are normalized with the same fixed set of
`True`/`False` laws, then compared up to grouping and equality orientation.
Quantifiers over a constant body use the local `Nonempty` sort instances. -/
def reduceFalseTrue (input : RuleInput) : MetaM (Option Expr) := do
  let some parentProof ← singleFormulaParent? input | return none
  let source ← inferType parentProof
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar
      (mkForall `vampireTrueFalseSource .default source input.target)
    | return none
  try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
      (intro vampireTrueFalseSource;
       try simp only [true_and, and_true, false_and, and_false,
         true_or, or_true, false_or, or_false,
         not_true_eq_false, not_false_eq_true, Classical.not_not,
         true_implies, false_implies, implies_true, imp_false,
         true_iff, iff_true, false_iff, iff_false,
         forall_const, exists_const, exists_false] at vampireTrueFalseSource ⊢;
       first
         | done
         | exact vampireTrueFalseSource
         | symm_match using vampireTrueFalseSource
         | (simp only [or_assoc, and_assoc] at vampireTrueFalseSource ⊢;
            symm_match using vampireTrueFalseSource))))
    unless remaining.isEmpty do return none
    let proof := mkApp (← instantiateMVars (.mvar goal)) parentProof
    -- `simp` may unfold proof-local lets while rewriting.
    withConfig (fun config => { config with zetaDelta := true }) <|
      asExpectedType proof input.target
  catch error =>
    trace[vampire.replay] "true/false elimination failed: {error.toMessageData}"
    pure none

/-- Prove `target` from `proof : source`, where both are the same clause
`∀ x̄, L₁ ∨ … ∨ Lₙ` except that some literals are complemented through a
polarity-flip `let` `p_flipped := fun x̄ => ¬ p x̄`. A negative literal `¬p t̄`
already is `p_flipped t̄`; a positive literal `p t̄` becomes
`¬p_flipped t̄`, i.e. `¬¬p t̄`. Expects let unfolding to be enabled. -/
private partial def flipClause (proof source target : Expr) : MetaM (Option Expr) := do
  let source := (← instantiateMVars source).consumeMData
  let target := (← instantiateMVars target).consumeMData
  if ← isDefEq source target then return some proof
  if let .forallE name domain sourceBody _ := source then
    if let .forallE _ targetDomain targetBody _ := target then
      if ← ((do return !(← isProp domain)) <&&> isDefEq domain targetDomain) then
        return ← withLocalDeclD name domain fun binder => do
          let some body ← flipClause (mkApp proof binder)
              (sourceBody.instantiate1 binder) (targetBody.instantiate1 binder)
            | return none
          some <$> mkLambdaFVars #[binder] body
  match source.app2? ``Or, target.app2? ``Or with
  | some (sourceLeft, sourceRight), some (targetLeft, targetRight) =>
    let side (sourceSide targetSide : Expr) : MetaM (Option Expr) :=
      withLocalDeclD `literal sourceSide fun literal => do
        let some proof ← flipClause literal sourceSide targetSide | return none
        some <$> mkLambdaFVars #[literal] proof
    let some left ← side sourceLeft targetLeft | return none
    let some right ← side sourceRight targetRight | return none
    return some (← mkAppM ``Or.imp #[left, right, proof])
  | _, _ =>
    -- A flipped positive literal: `L → ¬¬L`.
    unless ← isDefEq target (mkNot (mkNot source)) do return none
    let doubleNegation ← withLocalDeclD `negated (mkNot source) fun negated =>
      mkLambdaFVars #[negated] (mkApp negated proof)
    asExpectedType doubleNegation target

/-- Reconstruct `consistent_polarity_flipping`. Replay has already bound each
flipped predicate to its `p_flipped` let in this conclusion, so the step is
the implication proved by `flipClause`. -/
def polarityFlipping (input : RuleInput) : MetaM (Option Expr) := do
  let some parentProof ← singleFormulaParent? input | return none
  withConfig (fun config => { config with zetaDelta := true }) do
    -- lean-auto spells `∀` as a beta-redex of its quantifier combinator.
    let source ← Core.betaReduce (← instantiateMVars (← inferType parentProof))
    let target ← Core.betaReduce (← instantiateMVars input.target)
    let some proof ← flipClause parentProof source target | return none
    asExpectedType proof input.target

end VampireHammer.Backend
