import VampireHammer.Backend.Common
import VampireHammer.Backend.Instantiation

/-! Higher-order inference handlers: Boolean equality normalization,
certified instantiation and extensionality, and clause equality rules. Every
candidate is checked against the displayed target. -/
namespace VampireHammer.Backend
open Lean Meta
open Internal

/-- A total difference function. On equal functions it chooses an arbitrary
domain element; on unequal functions its specification gives a counterexample. -/
noncomputable def differenceWitness {α β : Sort _} [Nonempty α] (f g : α → β) : α :=
  Classical.epsilon (fun x => f x ≠ g x)

theorem differenceWitness_spec {α β : Sort _} [Nonempty α]
    {f g : α → β} (h : f ≠ g) : f (differenceWitness f g) ≠ g (differenceWitness f g) := by
  apply Classical.epsilon_spec_aux _ (fun x => f x ≠ g x)
  apply Classical.byContradiction
  intro absent
  apply h
  funext x
  exact Classical.byContradiction (fun different => absent ⟨x, different⟩)

theorem fool_eq_true (p : Prop) : (p = True) ↔ p := by
  constructor
  · intro h; exact h ▸ True.intro
  · intro h; exact propext ⟨fun _ => True.intro, fun _ => h⟩

theorem fool_eq_false (p : Prop) : (p = False) ↔ ¬p := by
  constructor
  · intro h; exact h ▸ id
  · intro h; exact propext ⟨h, False.elim⟩

theorem fool_true_eq (p : Prop) : (True = p) ↔ p := by
  rw [eq_comm]; exact fool_eq_true p

theorem fool_false_eq (p : Prop) : (False = p) ↔ ¬p := by
  rw [eq_comm]; exact fool_eq_false p

theorem higherOrderMapHead {p q : Prop} (tail : List Prop) (step : p → q)
    (h : VampireHammer.Clause.Holds (p :: tail)) :
    VampireHammer.Clause.Holds (q :: tail) :=
  Or.elim h (fun head => Or.inl (step head)) Or.inr

theorem positiveExtensionalityHead {α β : Sort _} (tail : List Prop) (f g : α → β)
    (h : ∀ x, VampireHammer.Clause.Holds ((f x = g x) :: tail)) :
    VampireHammer.Clause.Holds ((f = g) :: tail) := by
  classical
  by_cases rest : VampireHammer.Clause.Holds tail
  · exact Or.inr rest
  · exact Or.inl (funext fun x => (h x).resolve_right rest)

private def formulaParent? (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  if parent.clauseForm then
    fromClauseForm parent.proof parent.target parent.binders.size parent.clauseLiterals?
  else pure (some parent.proof)

/-- Check a printed higher-order instance, with beta/eta conversion and
literal reordering only. Imitation/projection steps with additional residual
constraints need a different certificate and are deliberately declined. -/
def higherOrderInstantiation (input : RuleInput)
    (substitutions : Array ParentSubstitution) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) do return none
  let some substitutions := orderParentSubstitutions input.parents substitutions | return none
  underConclusionBinders input fun bindings _ => do
    let some instantiated ← instantiateParents input substitutions bindings | return none
    let some (proof, type) := instantiated[0]? | return none
    let some source ← resolutionClauseView proof type | return none
    unless !source.isAClause do return none
    let some target := targetClauseLiterals? input bindings | return none
    VampireHammer.ClauseMeta.reorderAndNormalize proof source.regular.toList target.toList

/-- A flex-flex closure needs a printed common instance of its flexible
heads. Verify that every residual disequality is reflexive in that instance. -/
def higherOrderFlexFlex (input : RuleInput)
    (substitutions : Array ParentSubstitution) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      input.parents.all (·.clauseForm) do return none
  let some substitutions := orderParentSubstitutions input.parents substitutions | return none
  underConclusionBinders input fun bindings target => do
    unless ← isDefEq target (mkConst ``False) do return none
    let some instantiated ← instantiateParents input substitutions bindings | return none
    let some (proof, type) := instantiated[0]? | return none
    let some view ← resolutionClauseView proof type | return none
    unless !view.isAClause do return none
    let mut allFalse := mkConst ``VampireHammer.Clause.AllFalse.nil
    let mut tail := ([] : List Expr)
    for literal in view.regular.toList.reverse do
      let some equation ← notArgument? literal | return none
      let some (_, left, right) := equation.eq? | return none
      unless ← isDefEq left right do return none
      let refutation ← withLocalDeclD `flexConstraint literal fun assumption => do
        mkLambdaFVars #[assumption] (mkApp assumption (← mkEqRefl left))
      allFalse ← mkAppM ``VampireHammer.Clause.AllFalse.cons
        #[literal, ← mkListLit (mkSort .zero) tail, refutation, allFalse]
      tail := literal :: tail
    asExpectedType (← mkAppM ``VampireHammer.Clause.AllFalse.notHolds #[allFalse, view.proof]) target

/-- Fixed Boolean identities suffice for the initial FOOL fragment. No
unifier search or unrelated source hypotheses participate in this proof. -/
def foolElimination (input : RuleInput) : MetaM (Option Expr) := do
  -- Fresh FOOL conditional symbols are checked local lets. Eliminating them
  -- preserves the first parent's formula by unfolding precisely those lets;
  -- the additional definition parents have already been checked in the DAG.
  if input.sourceProof?.isNone then
    if let some first := input.parents[0]? then
      if !first.clauseForm then
        if let some proof ← withConfig (fun config => { config with zetaDelta := true }) <|
            asExpectedType first.proof input.target then return some proof
  let some parent ← formulaParent? input | return none
  let source ← inferType parent
  let .mvar goal ← mkFreshExprSyntheticOpaqueMVar
      (mkForall `foolSource .default source input.target) | return none
  try
    let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
      (intro foolSource;
       simp only [fool_eq_true, fool_eq_false, fool_true_eq, fool_false_eq] at foolSource ⊢;
       exact foolSource)))
    unless remaining.isEmpty do return none
    asExpectedType (mkApp (← instantiateMVars (.mvar goal)) parent) input.target
  catch _ => pure none

private partial def literalCount (formula : Expr) : Nat :=
  match formula.app2? ``Or with
  | some (left, right) => literalCount left + literalCount right
  | none => 1

private partial def transportDifference (proof source target : Expr) (selected : Nat) :
    MetaM (Option Expr) := do
  match source.app2? ``Or, target.app2? ``Or with
  | some (sl, sr), some (tl, tr) =>
    let count := literalCount sl
    let side (sourceSide targetSide : Expr) (active : Bool) (index : Nat) : MetaM (Option Expr) :=
      withLocalDeclD `differenceLiteral sourceSide fun h => do
        let candidate ← if active then transportDifference h sourceSide targetSide index
          else asExpectedType h targetSide
        let some candidate := candidate | return none
        some <$> mkLambdaFVars #[h] candidate
    let some left ← side sl tl (selected < count) selected | return none
    let some right ← side sr tr (selected ≥ count) (selected - count) | return none
    some <$> mkAppM ``Or.imp #[left, right, proof]
  | none, none =>
    unless selected == 0 do return none
    let some equality ← notArgument? source | do
      trace[vampire.replay] "negative extensionality: not a disequality: {source}"
      return none
    unless equality.eq?.isSome do return none
    let candidate ← mkAppM ``differenceWitness_spec #[proof]
    let result ← asExpectedType candidate target
    if result.isNone then
      trace[vampire.replay] "negative extensionality: witness mismatch: {← inferType candidate} versus {target}"
    pure result
  | _, _ => pure none

/-- Preserve every clause literal except the certified disequality, applying
the optional bijection from parent binders to the child scope. -/
def negativeExtensionality (input : RuleInput) (info : NegativeExtensionalityInfo) :
    MetaM (Option Expr) := do
  let some parent := input.parents[0]? | return none
  unless parent.parent.name == info.literal.parent &&
      (witnessDependencyIndices? (parent.binders.map (·.name)) info.dependencies).isSome do return none
  let some positions := witnessBinderIndices? (parent.binders.map (·.name))
    (input.step.binders.map (·.name)) info.binderMapping? | return none
  let some proof ← formulaParent? input | return none
  try
    withConfig (fun config => { config with zetaDelta := true }) do
      underConclusionBinders input fun bindings target => do
        let mut applied := proof
        for index in positions do
          let argument := bindings[index]!.2
          let type ← whnf (← inferType applied)
          unless ← (pure type.isForall <&&>
              (do isDefEq type.bindingDomain! (← inferType argument))) do
            return none
          applied := mkApp applied argument
        let source ← Core.betaReduce (← inferType applied)
        let target ← Core.betaReduce target
        let some body ← transportDifference applied source target info.literal.index | return none
        asExpectedType body target
  catch error =>
    trace[vampire.replay] "negative extensionality declined: {error.toMessageData}"
    pure none

private partial def extendEquality (proof sourceLeft sourceRight targetLeft targetRight : Expr) :
    MetaM (Option Expr) := do
  if ← (isDefEq sourceLeft targetLeft <&&> isDefEq sourceRight targetRight) then
    return some proof
  let .app lf la := targetLeft.consumeMData | return none
  let .app rf ra := targetRight.consumeMData | return none
  unless ← isDefEq la ra do return none
  let some fn ← extendEquality proof sourceLeft sourceRight lf rf | return none
  some <$> mkAppM ``congrFun #[fn, la]

/-- Apply retained parent binders by name and optionally abstract one removed
extensionality variable. All applications check their domains. -/
private partial def withEqualityParent (proof : Expr) (binders : List FormulaBinder)
    (bindings : Array (String × Expr)) (removed : Option String) (variable? : Option Expr)
    (k : Expr → Option Expr → MetaM (Option Expr)) : MetaM (Option Expr) := do
  match binders with
  | [] => k proof variable?
  | binder :: rest =>
    let type ← whnf (← inferType proof)
    unless type.isForall do return none
    if removed == some binder.name then
      withLocalDeclD (Name.mkSimple binder.name) type.bindingDomain! fun argument => do
        let some body ← withEqualityParent (mkApp proof argument) rest bindings removed
            (some argument) k | return none
        some <$> mkLambdaFVars #[argument] body
    else
      let some (_, argument) := bindings.find? (·.1 == binder.name) | return none
      unless ← isDefEq (← inferType argument) type.bindingDomain! do return none
      withEqualityParent (mkApp proof argument) rest bindings removed variable? k

/-- Reconstruct equality rules in a regular clause with all other literal
occurrences retained. For extensionality one parent binder disappears; for
congruence the child may quantify additional application arguments. -/
private def higherOrderEqualityClause (input : RuleInput) (rule : String) : MetaM (Option Expr) := do
  let some parent := input.parents[0]? | return none
  unless parent.clauseForm && input.clauseLiterals?.isSome do return none
  let removed := parent.binders.filter fun binder => !input.step.binders.any (·.name == binder.name)
  if rule == "positive_extensionality" then
    unless removed.size == 1 do return none
  else unless removed.isEmpty do return none
  let removedName := removed[0]?.map (·.name)
  underConclusionBinders input fun bindings _ => do
    let some target := targetClauseLiterals? input bindings | return none
    for index in [:target.size] do
      let some (_, left, right) := target[index]!.eq? | continue
      let tail := target.eraseIdxIfInBounds index
      let prepared ← withNewMCtxDepth <| withEqualityParent parent.proof parent.binders.toList
          bindings removedName none fun proof variable? => do
        let some view ← resolutionClauseView proof (← inferType proof) | return none
        unless !view.isAClause && view.regular.size == target.size do return none
        if rule == "positive_extensionality" then
          let some argument := variable? | return none
          let selected ← mkEq (mkApp left argument) (mkApp right argument)
          VampireHammer.ClauseMeta.reorderAndNormalize view.proof view.regular.toList
            (selected :: tail.toList)
        else
          for sourceLiteral in view.regular do
            let some (_, u, v) := sourceLiteral.eq? | continue
            let some source ← VampireHammer.ClauseMeta.reorderAndNormalize view.proof
                view.regular.toList (sourceLiteral :: tail.toList) | continue
            let transition ← withLocalDeclD `functionEquality sourceLiteral fun equality => do
              let some result ← extendEquality equality u v left right | return none
              let some result ← asExpectedType result target[index]! | return none
              some <$> mkLambdaFVars #[equality] result
            let some transition := transition | continue
            return some (← mkAppM ``higherOrderMapHead
              #[← mkListLit (mkSort .zero) tail.toList, transition, source])
          pure none
      let some prepared := prepared | continue
      let proof ← if rule == "positive_extensionality" then
        mkAppM ``positiveExtensionalityHead
          #[← mkListLit (mkSort .zero) tail.toList, left, right, prepared]
      else pure prepared
      let some result ← VampireHammer.ClauseMeta.reorderAndNormalize proof
          (target[index]! :: tail.toList) target.toList | continue
      return some result
    pure none

def higherOrderEquality (input : RuleInput) (rule : String) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  let some proof ← if parent.clauseForm then
      fromClauseForm parent.proof parent.target parent.binders.size parent.clauseLiterals?
    else pure (some parent.proof)
    | return none
  try
    if let some proof ← higherOrderEqualityClause input rule then return some proof
    if rule == "positive_extensionality" then
      return ← asExpectedType (← mkAppM ``funext #[proof]) input.target
    unless rule == "argument_congruence" do return none
    forallTelescopeReducing input.target fun arguments body => do
      let mut result := proof
      for argument in arguments do
        result ← mkAppM ``congrFun #[result, argument]
      let some checked ← asExpectedType result body | return none
      let abstraction ← mkLambdaFVars arguments checked
      asExpectedType abstraction input.target
  catch _ => pure none

end VampireHammer.Backend
