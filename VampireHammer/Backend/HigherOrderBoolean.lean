import VampireHammer.Backend.HigherOrder
import VampireHammer.Backend.Occurrence

/-! Fixed Boolean normalization and propositional transport for HOL rules.
Only the displayed parent participates; there is no unification or grind. -/
namespace VampireHammer.Backend
open Lean Meta Elab Tactic
open Internal

theorem prop_eq_iff (p q : Prop) : (p = q) ↔ (p ↔ q) :=
  ⟨Iff.of_eq, propext⟩

theorem prop_not_diseq_left (p q : Prop) : (¬p) ≠ q ↔ p = q := by
  classical
  by_cases hp : p <;> by_cases hq : q <;> simp [hp, hq]

theorem prop_not_diseq_right (p q : Prop) : p ≠ (¬q) ↔ p = q := by
  rw [ne_comm, prop_not_diseq_left, eq_comm]

theorem booleanCasesClause (p : Prop) (context : Prop → List Prop)
    (h : VampireHammer.Clause.Holds (context p)) :
    VampireHammer.Clause.Holds (context True ++ [p = False]) := by
  classical
  by_cases hp : p
  · have equality : p = True := (fool_eq_true p).mpr hp
    apply VampireHammer.Clause.appendLeft
    exact equality ▸ h
  · apply VampireHammer.Clause.appendRight
    exact Or.inl ((fool_eq_false p).mpr hp)

theorem booleanCasesFalseClause (p : Prop) (context : Prop → List Prop)
    (h : VampireHammer.Clause.Holds (context p)) :
    VampireHammer.Clause.Holds (context False ++ [p = True]) := by
  classical
  by_cases hp : p
  · apply VampireHammer.Clause.appendRight
    exact Or.inl ((fool_eq_true p).mpr hp)
  · have equality : p = False := (fool_eq_false p).mpr hp
    apply VampireHammer.Clause.appendLeft
    exact equality ▸ h

/-- Replace all occurrences of the certified subterm in one selected
literal, retaining the rest of the clause and adding the opposite truth case. -/
def higherOrderBooleanCase (input : RuleInput) (info : BooleanCaseInfo) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  unless parent.clauseForm && parent.parent.name == info.literal.parent &&
      parent.binders.map (·.name) == input.step.binders.map (·.name) do return none
  let substitutions := #[{ parent := parent.parent.name, bindings := #[] : ParentSubstitution }]
  underConclusionBinders input fun bindings _ => do
    let some scope ← instantiationScope input substitutions bindings | return none
    let some parents ← instantiateParentsIn input substitutions bindings scope | return none
    let some (proof, type) := parents[0]? | return none
    let some view ← resolutionClauseView proof type | return none
    unless !view.isAClause do return none
    let some selected := view.regular[info.literal.index]? | return none
    let some terms ← materializeTermsIn input bindings scope #[info.term] | return none
    let some term := terms[0]? | return none
    unless ← isProp term do return none
    let context? ← withLocalDeclD `booleanValue (mkSort .zero) fun value => do
      let some rewritten ← rewriteTermOccurrences term value selected info.occurrence? | return none
      let body ← mkListLit (mkSort .zero)
        (view.regular.set! info.literal.index rewritten).toList
      some <$> mkLambdaFVars #[value] body
    let some context := context? | return none
    let truth := mkConst (if info.replaceWithTrue then ``True else ``False)
    let opposite := mkConst (if info.replaceWithTrue then ``False else ``True)
    let some replaced ← rewriteTermOccurrences term truth selected info.occurrence? | return none
    unless replaced != selected do return none
    let natural := (view.regular.set! info.literal.index replaced).push (← mkEq term opposite)
    let theoremName := if info.replaceWithTrue then ``booleanCasesClause else ``booleanCasesFalseClause
    let result ← mkAppM theoremName #[term, context, proof]
    let some target := targetClauseLiterals? input bindings | return none
    VampireHammer.ClauseMeta.reorderAndNormalize result natural.toList target.toList

private def formulaParent (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  if parent.clauseForm then
    fromClauseForm parent.proof parent.target parent.binders.size parent.clauseLiterals?
  else pure (some parent.proof)

/-- Structural propositional consequence. Split only disjunctions already in
the source, project conjunctions, and inject into the displayed target.
The fuel bound limits work; every successful branch returns a Lean proof. -/
private def propositionalTransport (facts : Array Expr) (target : Expr)
    (arguments : Array Expr := #[]) :
    Nat → MetaM (Option Expr)
  | 0 => pure none
  | fuel + 1 => do
    for fact in facts do
      if let some proof ← asExpectedType fact target then return some proof
      if let some equivalent ← VampireHammer.ClauseMeta.literalEquivalent? (← inferType fact) target then
        return some (← mkAppM ``Iff.mp #[equivalent, fact])
    let reducedTarget ← whnfR target
    if reducedTarget.isForall then
      let domain := reducedTarget.bindingDomain!
      return ← withLocalDeclD reducedTarget.bindingName! domain fun argument => do
        let mut instantiated := facts
        if ← isProp domain then instantiated := instantiated.push argument
        let some proof ← propositionalTransport instantiated
            (reducedTarget.bindingBody!.instantiate1 argument) (arguments.push argument) fuel | return none
        some <$> mkLambdaFVars #[argument] proof
    if ← isDefEq target (mkConst ``True) then return some (mkConst ``True.intro)
    for fact in facts do
      let source ← inferType fact
      if ← isDefEq source (mkConst ``False) then
        return some (← mkFalseElim target fact)
      if let some negative ← notArgument? source then
        for other in facts do
          if ← isDefEq (← inferType other) negative then
            return some (← mkFalseElim target (mkApp fact other))
    for index in [:facts.size] do
      let fact := facts[index]!
      let source ← whnfR (← inferType fact)
      if source.isForall then
        for argument in arguments do
          if ← isDefEq source.bindingDomain! (← inferType argument) then
            if let some result ← propositionalTransport
                (facts.set! index (mkApp fact argument)) target arguments fuel then
              return some result
      if let some (_, _) := source.app2? ``And then
        let left ← mkAppM ``And.left #[fact]
        let right ← mkAppM ``And.right #[fact]
        return ← propositionalTransport (facts.eraseIdxIfInBounds index ++ #[left, right]) target arguments fuel
      if let some (left, right) := source.app2? ``Or then
        let branch (proposition : Expr) : MetaM (Option Expr) :=
          withLocalDeclD `booleanBranch proposition fun value => do
            let some proof ← propositionalTransport
                (facts.eraseIdxIfInBounds index |>.push value) target arguments fuel | return none
            some <$> mkLambdaFVars #[value] proof
        let some leftProof ← branch left | return none
        let some rightProof ← branch right | return none
        return some (← mkAppM ``Or.elim #[fact, leftProof, rightProof])
    if let some (left, right) := target.app2? ``Or then
      if let some proof ← propositionalTransport facts left arguments fuel then
        return some (← mkAppOptM ``Or.inl #[left, right, proof])
      if let some proof ← propositionalTransport facts right arguments fuel then
        return some (← mkAppOptM ``Or.inr #[left, right, proof])
    if let some (left, right) := target.app2? ``And then
      let some leftProof ← propositionalTransport facts left arguments fuel | return none
      let some rightProof ← propositionalTransport facts right arguments fuel | return none
      return some (← mkAppM ``And.intro #[leftProof, rightProof])
    pure none

/-- Normalize with a fixed list of logical identities, then structurally
check the resulting implication. This also rewrites propositions used as
higher-order arguments and beneath lambdas through propositional extensionality. -/
def higherOrderBooleanTransport (parent target : Expr) : MetaM (Option Expr) := do
  if let some proof ← asExpectedType parent target then return some proof
  let source ← inferType parent
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar (← mkArrow source target) | return none
  let sourceName := mkIdent (← mkFreshUserName `booleanSource)
  try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
      (classical
       intro $sourceName:ident
       try simp only [prop_not_diseq_left, prop_not_diseq_right,
         prop_eq_iff, fool_eq_true, fool_eq_false, fool_true_eq, fool_false_eq,
         true_and, and_true, false_and, and_false, and_self,
         true_or, or_true, false_or, or_false, or_self,
         not_true_eq_false, not_false_eq_true, Classical.not_not,
         true_implies, false_implies, implies_true, imp_false, imp_self,
         true_iff, iff_true, false_iff, iff_false, iff_self,
         and_not_self_iff, not_and_self_iff, Decidable.or_not_self, Decidable.not_or_self,
         Classical.not_and_iff_not_or_not, not_or, Classical.not_imp_iff_and_not,
         Classical.not_forall, not_exists,
         Decidable.imp_iff_not_or,
         iff_iff_implies_and_implies, eq_self, or_assoc, and_assoc]
         at $sourceName:ident ⊢)))
    for pending in remaining do
      pending.withContext do
        let mut sourceProof? := none
        for declaration in ← getLCtx do
          if declaration.userName == sourceName.getId then
            sourceProof? := some declaration.toExpr
        let some sourceProof := sourceProof? | throwError "missing Boolean source"
        let some proof ← propositionalTransport #[sourceProof] (← pending.getType) #[] 128
          | throwError "unsupported Boolean consequence"
        pending.assign proof
    asExpectedType (mkApp (← instantiateMVars (.mvar goal)) parent) target
  catch error =>
    trace[vampire.replay] "Boolean reconstruction declined: {error.toMessageData}"
    pure none

def higherOrderBoolean (input : RuleInput) : MetaM (Option Expr) := do
  let some parent ← formulaParent input | return none
  higherOrderBooleanTransport parent input.target

/-- Input nodes require equivalence, not a weaker consequence. Check both
directions, including cases that simp closes outright. -/
def higherOrderBooleanEquivalent (proof target : Expr) : MetaM (Option Expr) := do
  let some forward ← higherOrderBooleanTransport proof target | return none
  let source ← inferType proof
  let reverseChecked ← withLocalDeclD `booleanTarget target fun assumedTarget => do
    pure (← higherOrderBooleanTransport assumedTarget source).isSome
  if reverseChecked then pure (some forward) else pure none

def higherOrderNormalization (input : RuleInput) : MetaM (Option Expr) := do
  let some parent ← formulaParent input | return none
  higherOrderBooleanEquivalent parent input.target

/-- Leibniz elimination specializes its predicate variable and removes the
reflexive Boolean literal produced by that specialization. -/
def higherOrderBooleanInstantiation (input : RuleInput)
    (substitutions : Array ParentSubstitution) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) do return none
  let some substitutions := orderParentSubstitutions input.parents substitutions | return none
  underConclusionBinders input fun bindings target => do
    let some parents ← instantiateParents input substitutions bindings | return none
    let some (proof, type) := parents[0]? | return none
    let some view ← resolutionClauseView proof type | return none
    unless !view.isAClause do return none
    let formula := view.regular.foldr mkOr (mkConst ``False)
    let some proof ← asExpectedType proof formula | return none
    higherOrderBooleanTransport proof target

end VampireHammer.Backend
