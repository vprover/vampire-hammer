import VampireHammer.Backend.Common
import VampireHammer.Backend.Instantiation

/-!
Clause-level preprocessing that names subterms or subclauses with fresh
symbols: general splitting, inequality splitting, and the equality proxy.

`Replay` binds every fresh symbol to the value read off its definition node
(`predicateDefinitionValue?`), so these steps need no certificate:

* general splitting: `sP := fun x̄ => ¬ ∀ y, M`;
* inequality splitting: `sP := fun x => x ≠ t`;
* equality proxy: `sQ := fun x y => x = y`.

The handlers unfold those lets (`zetaDelta`) and return clause-form proofs.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- The value of a fresh symbol applied to its arguments, beta-reduced. -/
private def unfoldSymbolApp (application : Expr) : MetaM (Option Expr) := do
  let some symbol := application.getAppFn.fvarId? | return none
  let some value ← symbol.getValue? | return none
  some <$> Core.betaReduce (mkAppN value application.getAppArgs)

/-- For a general-splitting name literal `sP x̄`, the component `fun y => M y`
as a function to its clause tree, with the binder's name and domain. -/
private def splittingComponent? (nameLiteral : Expr) :
    MetaM (Option (Name × Expr × Expr)) := do
  let some unfolded ← unfoldSymbolApp nameLiteral | return none
  let some all := unfolded.not? | return none
  let .forallE name domain body _ := all | return none
  let component ← withLocalDeclD name domain fun y => do
    mkLambdaFVars #[y] (← clauseTree (body.instantiate1 y))
  pure (some (name, domain, component))

/-- Read a concrete `List Prop`, reducing (for example a tree's `literals`)
as needed. -/
private partial def propList? (list : Expr) (acc : Array Expr := #[]) :
    MetaM (Option (Array Expr)) := do
  let list ← whnf list
  if list.isAppOfArity ``List.nil 1 then return some acc
  if list.isAppOfArity ``List.cons 3 then
    return ← propList? list.appArg! (acc.push list.appFn!.appArg!)
  pure none

/-- Literal-wise definitional equality of two clauses. -/
private def sameLiterals (left right : Array Expr) : MetaM Bool := do
  unless left.size == right.size do return false
  for (l, r) in left.zip right do
    unless ← isDefEq l r do return false
  pure true

/-- Reconstruct a general-splitting component clause `M y ∨ sP x̄`, printed as
`cnf_transformation` of the definition `sP x̄ ↔ ¬ ∀ y, M y`. The split variable `y` is
the conclusion binder for which the leading literals are exactly `M y`. -/
def splittingComponentClause (input : RuleInput) : MetaM (Option Expr) :=
  withConfig (fun config => { config with zetaDelta := true }) do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  underConclusionBinders input fun bindings _target => do
    let some target := targetClauseLiterals? input bindings | return none
    let some nameLiteral := target.back? | return none
    let some (_, domain, component) ← splittingComponent? nameLiteral | return none
    for (_, y) in bindings do
      unless ← isDefEq (← inferType y) domain do continue
      -- Compare via the tree's literal list, which is what the lemma states.
      let treeLiterals ← whnf (← mkAppM ``VampireHammer.Clause.Tree.literals #[mkApp component y])
      let some listed ← propList? treeLiterals | continue
      unless ← sameLiterals listed target.pop do continue
      let core ← mkAppM ``VampireHammer.Clause.splittingComponent #[component, y]
      if let some proof ← asExpectedType core (← holdsType target) then
        trace[vampire.replay] "general splitting component {input.step.name}: split variable {y}"
        return some proof
    pure none

/-- Reconstruct the remainder `O ∨ ¬ sP x̄` of general splitting from the split
clause `∀ y, M y ∨ O` (first parent; the others are the definitions). The
split variable is the one parent binder that the conclusion does not bind;
the parent's literals are permuted to `M y ++ O` before `splittingRemainder`. -/
def generalSplitting (input : RuleInput) : MetaM (Option Expr) :=
  withConfig (fun config => { config with zetaDelta := true }) do
  unless input.sourceProof?.isNone && input.parents.size ≥ 2 do return none
  let some base := input.parents[0]? | return none
  unless base.clauseForm do return none
  underConclusionBinders input fun bindings _target => do
    let some target := targetClauseLiterals? input bindings | return none
    let some negatedName := target.back? | return none
    let some nameLiteral := negatedName.not? | return none
    let some (name, domain, component) ← splittingComponent? nameLiteral | return none
    let rest := target.pop
    let unbound := base.binders.filter fun binder => !bindings.any (·.1 == binder.name)
    let #[splitBinder] := unbound | return none
    let baseInstance ← withLocalDeclD name domain fun y => do
      let arguments := base.binders.map fun binder =>
        if binder.name == splitBinder.name then y
        else ((bindings.find? (·.1 == binder.name)).map (·.2)).getD y
      let instantiated := mkAppN base.proof arguments
      let some (_, baseLiterals) ← clauseView instantiated (← inferType instantiated)
        | return none
      let componentLiterals ← flattenClause (← Core.betaReduce
        (← mkAppM ``VampireHammer.Clause.Tree.denote #[mkApp component y]))
      let some reordered ← reorderAndNormalize instantiated baseLiterals.toList
          (componentLiterals ++ rest).toList
        | return none
      some <$> mkLambdaFVars #[y] reordered
    let some baseInstance := baseInstance | return none
    let restList := mkPropList rest.toList
    let core ← mkAppM ``VampireHammer.Clause.splittingRemainder
      #[component, restList, baseInstance]
    let result ← asExpectedType core (← holdsType target)
    if result.isSome then
      trace[vampire.replay] "general splitting {input.step.name}: split off variable {splitBinder.name}"
    pure result

/-- Transport the first parent to the conclusion literal by literal, after
unfolding fresh-symbol lets, allowing equality orientation. This covers
`equality_proxy_replacement` (`x = y` becomes `sQ x y`) and
`inequality_splitting` (`s ≠ t` or `t ≠ s` becomes `sP s`); the remaining
parents are the definitions. -/
def definitionalClauseTransport (input : RuleInput) (rule : String) : MetaM (Option Expr) :=
  withConfig (fun config => { config with zetaDelta := true }) do
  unless input.sourceProof?.isNone && input.parents.size ≥ 1 do return none
  let some parent := input.parents[0]? | return none
  unless parent.clauseForm do return none
  let single := { input with parents := #[parent] }
  underConclusionBinders single fun bindings _target => do
    let some instantiated ← instantiateParents single
        #[{ parent := parent.parent.name, bindings := #[] }] bindings
      | return none
    let some (proof, type) := instantiated[0]? | return none
    let some view ← resolutionClauseView proof type | return none
    if view.isAClause then return none
    let some target := targetClauseLiterals? single bindings | return none
    let some transported ← normalizeRegularEqualityResult view.proof view.regular target
      | return none
    -- State the result at the displayed clause type: the caller compares
    -- with fresh-symbol lets folded.
    let result ← asExpectedType transported (← holdsType target)
    if result.isSome then
      trace[vampire.replay] "{rule} {input.step.name}: parent clause up to definitions and orientation"
    pure result

/-- Reconstruct an `equality_proxy_axiom` (reflexivity, symmetry,
transitivity or congruence of `sQ := fun x y => x = y`). Its literals are
`¬A₁ … ¬Aₖ` and at most one positive `B`; assuming the clause fails yields
each `Aᵢ` and `¬B`, and `Aᵢ → B` closes by substituting the variable
equations. -/
def equalityProxyAxiom (input : RuleInput) : MetaM (Option Expr) :=
  withConfig (fun config => { config with zetaDelta := true }) do
  unless input.sourceProof?.isNone do return none
  underConclusionBinders input fun bindings _target => do
    let some target := targetClauseLiterals? input bindings | return none
    let reduce (literal : Expr) : MetaM Expr := do
      Core.betaReduce (← zetaReduce (← instantiateMVars literal))
    let mut negatives := #[]
    let mut positive? := none
    for literal in target do
      let reduced ← reduce literal
      if let some atom := reduced.not? then
        negatives := negatives.push atom
      else if positive?.isNone then
        positive? := some reduced
      else
        return none
    let conclusion := positive?.getD (mkConst ``False)
    -- `A₁ → … → Aₖ → B`, proved by substitution.
    let implicationType ← withLocalDecls negatives fun hypotheses =>
      mkForallFVars hypotheses conclusion
    let .mvar goal ← mkFreshExprSyntheticOpaqueMVar implicationType | return none
    let implication? ← try
      let (remaining, _) ← Lean.Elab.runTactic goal (← `(tactic|
        (intros; subst_vars; first | rfl | assumption | contradiction)))
      if remaining.isEmpty then pure (some (← instantiateMVars (.mvar goal))) else pure none
    catch error =>
      trace[vampire.replay] "equality proxy axiom {input.step.name}: {error.toMessageData}"
      pure none
    let some implication := implication? | return none
    -- From `¬ Holds target`, read off every literal's negation in order.
    let holds ← holdsType target
    let proof ← withLocalDeclD `notClause (mkNot holds) fun notClause => do
      let mut remaining := notClause
      let mut atoms := #[]
      let mut negatedConclusion? := none
      for index in [:target.size] do
        let literal := target[index]!
        let rest := mkPropList (target.toList.drop (index + 1))
        let notLiteral ← mkAppM ``VampireHammer.Clause.notHeadOfNotHolds
          #[literal, rest, remaining]
        if (← reduce literal).not?.isSome then
          -- `¬¬A` gives `A`.
          let atom := (← reduce literal).not?.get!
          atoms := atoms.push (← mkAppOptM ``Classical.byContradiction #[atom, notLiteral])
        else
          negatedConclusion? := some notLiteral
        remaining ← mkAppM ``VampireHammer.Clause.notTailOfNotHolds #[literal, rest, remaining]
      let derived := mkAppN implication atoms
      let contradiction := match negatedConclusion? with
        | some negated => mkApp negated derived
        | none => derived
      mkLambdaFVars #[notClause] contradiction
    let proof ← mkAppOptM ``Classical.byContradiction #[holds, proof]
    let result ← asExpectedType proof holds
    if result.isSome then
      trace[vampire.replay] "equality proxy axiom {input.step.name}: {negatives.size} hypothesis literal(s)"
    pure result
where
  withLocalDecls {α} (types : Array Expr) (k : Array Expr → MetaM α) : MetaM α :=
    let rec go (index : Nat) (fvars : Array Expr) : MetaM α := do
      if h : index < types.size then
        withLocalDeclD ((`hypothesis).appendIndexAfter index) types[index] fun fvar =>
          go (index + 1) (fvars.push fvar)
      else k fvars
    go 0 #[]

end VampireHammer.Backend
