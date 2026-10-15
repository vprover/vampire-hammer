import VampireHammer.Backend.Common
import VampireHammer.Backend_Preprocessing

/-!
Proof-local AVATAR and formula-naming definitions, and definition folding.

Replay has already introduced each certified fresh symbol as a local let.
These handlers check the parsed definition against that let and construct the
corresponding local proof; they do not introduce symbols into the replay DAG.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Reconstruct a proof-local AVATAR definition.

`Replay` has already introduced `symbol` as a local let whose value is the
component proposition. The parsed node still contains the explicit
`symbol ↔ component` formula; after unfolding that one let, `Iff.rfl` has
exactly the required type. Checking that the symbol occurs as a literal side
before definitional reduction prevents an unrelated tautological equivalence
from being accepted as its declaration. -/
def avatarDefinition (input : RuleInput) (info : AvatarDefinitionInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.isEmpty &&
      input.step.binders.isEmpty do return none
  let some symbol := input.symbols.get? info.symbol | return none
  let target ← whnf input.target
  let (.app (.app (.const ``Iff _) left) right) := target | return none
  unless left == symbol || right == symbol do return none
  unless ← isDefEq left right do return none
  let proof ← mkAppOptM ``Iff.rfl #[some left]
  asExpectedType proof input.target

/-- Reconstruct `definition_folding`, which replaces named subformulas of
its first parent by the predicates introduced for them; the remaining parents
are those definitions.  Since replay let-binds every named predicate to its
body, the conclusion is the first parent up to unfolding those lets (the
C++ checker's `change`), and up to equality orientation. -/
def definitionFolding (input : RuleInput) : MetaM (Option Expr) :=
  withConfig (fun config => { config with zetaDelta := true }) do
  unless input.sourceProof?.isNone do return none
  let some parent := input.parents[0]? | return none
  if parent.clauseForm then return none
  if let some proof ← asExpectedType parent.proof input.target then
    return some proof
  BackendPreprocessing.symmMatch parent.proof input.target

/-- The disjuncts of a proposition, read through beta-redexes. -/
private partial def disjuncts (proposition : Expr) : List Expr :=
  match proposition.headBeta.consumeMData with
  | .app (.app (.const ``Or _) left) right => disjuncts left ++ disjuncts right
  | other => [other]

/-- Prove a formula-naming definition `∀ x̄, φ x̄ ∨ ¬ sP x̄` (or the positive
spelling `ψ x̄ ∨ sP x̄`).

`Replay` has let-bound `sP` to `fun x̄ => φ x̄` (respectively
`fun x̄ => ¬ ψ x̄`), so `sP x̄` unfolds to the named body.  After opening the
binders, `Classical.em (sP x̄)` yields the definition with the named body as
one disjunct; `assocSymmMatch` then adapts it to Vampire's grouping.  This is
a fixed proof shape: unlike `grind`, it does not get lost in the named body. -/
def predicateDefinition (input : RuleInput) (info : PredicateDefinitionInfo) :
    MetaM (Option Expr) := withConfig (fun config => { config with zetaDelta := true }) do
  unless input.sourceProof?.isNone && input.parents.isEmpty do return none
  let some symbol := input.symbols.get? info.symbol | return none
  let some symbolId := symbol.fvarId? | return none
  let some value ← symbolId.getValue? | return none
  let rec go (target : Expr) (remaining : Nat) (opened : Array Expr) : MetaM (Option Expr) := do
    if remaining > 0 then
      let target ← whnf target
      unless target.isForall do return none
      return ← withLocalDeclD target.bindingName! target.bindingDomain! fun x => do
        let some body ← go (target.bindingBody!.instantiate1 x) (remaining - 1) (opened.push x)
          | return none
        pure (some (← mkLambdaFVars #[x] body))
    let isSymbolApp := fun (literal : Expr) => literal.getAppFn == symbol
    let some literal := (disjuncts target).find? fun literal =>
        isSymbolApp literal || (literal.not?.any isSymbolApp)
      | return none
    let negative := literal.not?.isSome
    let applied := literal.not?.getD literal
    let named ← Core.betaReduce (mkAppN value applied.getAppArgs)
    let em ← mkAppM ``Classical.em #[applied]
    let proof ← if negative then
      -- `named ∨ ¬ sP x̄`, where `sP x̄` unfolds to `named`.
      let notApplied := mkNot applied
      let motive := mkOr named notApplied
      let left ← withLocalDeclD `vampireNamed applied fun h => do
        mkLambdaFVars #[h] (mkApp3 (mkConst ``Or.inl) named notApplied h)
      let right ← withLocalDeclD `vampireNotNamed notApplied fun h => do
        mkLambdaFVars #[h] (mkApp3 (mkConst ``Or.inr) named notApplied h)
      pure (mkApp6 (mkConst ``Or.elim) applied notApplied motive em left right)
    else
      -- `ψ ∨ sP x̄`, where `sP x̄` unfolds to `named = ¬ ψ`.
      let some rest := named.not? | return none
      let motive := mkOr rest applied
      let left ← withLocalDeclD `vampireNamed applied fun h => do
        mkLambdaFVars #[h] (mkApp3 (mkConst ``Or.inr) rest applied h)
      let right ← withLocalDeclD `vampireNotNamed (mkNot applied) fun h => do
        let rest ← mkAppM ``Classical.byContradiction #[h]
        mkLambdaFVars #[h] (← mkAppM ``Or.inl #[rest])
      pure (mkApp6 (mkConst ``Or.elim) applied (mkNot applied) motive em left right)
    BackendPreprocessing.assocSymmMatch proof target
  let some proof ← go input.target input.step.binders.size #[] | return none
  asExpectedType proof input.target

/-- Reconstruct the parentless definition of a fresh symbol other than a
formula-naming predicate: `function_definition` (`sF x̄ = t`),
`equality_proxy_definition` (`sQ x y ↔ x = y`),
`general_splitting_component_introduction` (`(∀ y, M) ↔ ¬ sP x̄`) and
`inequality_splitting_name_introduction` (`¬ sP t`). Replay bound the symbol
to the value read off this very formula, so after unfolding it each holds by
reflexivity or double negation. -/
def symbolDefinition (input : RuleInput) (info : PredicateDefinitionInfo) :
    MetaM (Option Expr) := withConfig (fun config => { config with zetaDelta := true }) do
  unless input.sourceProof?.isNone && input.parents.isEmpty do return none
  unless input.symbols.contains info.symbol do return none
  let unfolded ← Core.betaReduce (← zetaReduce (← instantiateMVars input.target))
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar unfolded | return none
  try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
      (intros
       first
         | constructor <;> intros <;>
             (try apply Iff.of_eq
              first
                | exact Auto.Bool.ite'_eq_true _ _ _ (by assumption)
                | exact Auto.Bool.ite'_eq_false _ _ _ (by assumption)
                | exact (Auto.Bool.ite'_eq_true _ _ _ (by assumption)).symm
                | exact (Auto.Bool.ite'_eq_false _ _ _ (by assumption)).symm)
         | rfl
         | exact Iff.rfl
         | exact Classical.not_not.symm
         | exact Classical.not_not
         | exact fun h => h rfl)))
    unless remaining.isEmpty do return none
    asExpectedType (← instantiateMVars (.mvar goal)) input.target
  catch error =>
    trace[vampire.replay] "definition {input.step.name}: {error.toMessageData}"
    pure none

/-- Reconstruct `unused_predicate_definition_removal`: of an input definition
`∀ x̄, p x̄ ↔ φ`, keep the one implication (`p x̄ → φ` or `φ → p x̄`) that the
remaining occurrences of `p` need. -/
def unusedPredicateDefinitionRemoval (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  if parent.clauseForm then return none
  let binderCount := input.step.binders.size
  unless parent.binders.size == binderCount do return none
  -- lean-auto spells connectives and quantifiers as beta-redexes.
  let target ← Core.betaReduce (← instantiateMVars input.target)
  let proof? ← forallBoundedTelescope target (some binderCount) fun variables body => do
    unless variables.size == binderCount do return none
    let definition := mkAppN parent.proof variables
    let some (left, right) := (← whnfR (← Core.betaReduce (← inferType definition))).iff?
      | trace[vampire.replay] "unused predicate definition removal: parent is not an equivalence"
        return none
    let .forallE _ antecedent consequent _ := body
      | trace[vampire.replay] "unused predicate definition removal: conclusion {body} is not an implication"
        return none
    if consequent.hasLooseBVars then return none
    let implication ← if ← (isDefEq antecedent left <&&> isDefEq consequent right) then
      mkAppM ``Iff.mp #[definition]
    else if ← (isDefEq antecedent right <&&> isDefEq consequent left) then
      mkAppM ``Iff.mpr #[definition]
    else return none
    some <$> mkLambdaFVars variables implication
  let some proof := proof? | return none
  asExpectedType proof input.target

/-- Orientation of an input function definition `∀ x̄, f x̄ = t`: `true` when
the defined application `f x̄` (distinct bound arguments, `f` not in `t`) is
the left side. -/
private def definitionOrientation? (definition : Expr) : MetaM (Option Bool) := do
  forallTelescope (← instantiateMVars definition) fun variables body => do
    let some (_, left, right) := (← whnfR body).eq? | return none
    let defines (side other : Expr) : Bool :=
      let arguments := side.getAppArgs
      side.getAppFn.isFVar && !variables.contains side.getAppFn &&
        arguments.all variables.contains &&
        arguments.toList.eraseDups.length == arguments.size &&
        !other.containsFVar side.getAppFn.fvarId!
    if defines left right then return some true
    if defines right left then return some false
    pure none

/-- Reconstruct `definition_unfolding` (Vampire's function-definition
elimination): the first parent with every application of a defined symbol
rewritten by the remaining parents, the input definitions `∀ x̄, f x̄ = t`.
The single-parent internal-definition path removes wrappers interpreted by
Replay as equality/original predicates; it needs only structural transport. -/
def definitionUnfolding (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && !input.parents.isEmpty do return none
  let formula (parent : ParentProof) : MetaM (Option Expr) := do
    if parent.clauseForm then
      fromClauseForm parent.proof parent.target parent.binders.size parent.clauseLiterals?
    else pure (some parent.proof)
  let some first := input.parents[0]? | return none
  let some clause ← formula first | return none
  if input.parents.size == 1 then
    return ← withConfig (fun config => { config with zetaDelta := true }) do
      let result ← BackendPreprocessing.assocSymmMatch clause input.target
      if result.isSome then
        trace[vampire.replay] "definition unfolding {input.step.name}: removed internal definition wrappers"
      pure result
  let mut definitions := #[]
  for parent in input.parents[1:] do
    let some definition ← formula parent | return none
    let some forward ← definitionOrientation? (← inferType definition) | return none
    definitions := definitions.push (definition, forward)
  let names := (Array.range definitions.size).map fun index =>
    mkIdent (Name.mkSimple s!"vampireDefinition{index}")
  let rules ← (names.zip definitions).mapM fun (name, (_, forward)) =>
    if forward then `(Lean.Parser.Tactic.simpLemma| $name:term)
    else `(Lean.Parser.Tactic.simpLemma| ← $name:term)
  let types ← definitions.mapM fun (definition, _) => inferType definition
  let lemmaType ← withDefinitionHypotheses names types fun hypotheses => do
    mkForallFVars hypotheses (← mkArrow (← inferType clause) input.target)
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar lemmaType | return none
  try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
      (intro $names* vampireUnfoldedClause
       simp only [$rules,*] at vampireUnfoldedClause ⊢
       first
         | exact vampireUnfoldedClause
         | symm_match using vampireUnfoldedClause)))
    unless remaining.isEmpty do return none
    let lemma ← instantiateMVars (.mvar goal)
    trace[vampire.replay] "definition unfolding {input.step.name}: rewrote with {definitions.size} definition(s)"
    asExpectedType (mkAppN lemma (definitions.map (·.1) |>.push clause)) input.target
  catch error =>
    trace[vampire.replay] "definition unfolding {input.step.name}: {error.toMessageData}"
    pure none
where
  withDefinitionHypotheses {α} (names : Array Ident) (types : Array Expr)
      (k : Array Expr → MetaM α) : MetaM α :=
    let rec go (index : Nat) (fvars : Array Expr) : MetaM α := do
      if h : index < types.size then
        withLocalDeclD names[index]!.getId types[index] fun fvar =>
          go (index + 1) (fvars.push fvar)
      else k fvars
    go 0 #[]

end VampireHammer.Backend
