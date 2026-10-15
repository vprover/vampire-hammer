import VampireHammer.Backend.Common
import VampireHammer.Backend.Metadata
import VampireHammer.Backend_Skolemization
import VampireHammer.Backend_Preprocessing

/-!
Adapt `RuleInput` to the independent VampLean and Skolemization backends.

The actual logical transformations remain in `Backend_Preprocessing.lean` and
`Backend_Skolemization.lean`. These wrappers enforce replay phase conditions
and supply parent proofs, cached CNF clauses, binder names, and certificates.
-/

namespace VampireHammer.Backend

open Lean Meta Elab Tactic
open Auto.Embedding.Lam
open VampireHammer.ClauseMeta
open Internal

/-- Adapt the parser/replay structures to the independent Skolemization
backend.  The actual `Classical.choose_spec` proof lives in
`Backend_Skolemization.lean`; this wrapper only enforces the common replay
phase conditions and supplies the decoded metadata. -/
def skolemize (input : RuleInput) (info : SkolemizationInfo) :
    MetaM (Option Expr) := withConfig (fun config => { config with zetaDelta := true }) do
  unless input.sourceProof?.isNone && input.parents.size == 1 &&
      !storesClauseForm input do
    return none
  let some parent := input.parents[0]? | return none
  unless !parent.clauseForm && parent.existentialVariables.size == info.bindings.size do
    return none
  let some prenexed ← BackendSkolemization.existsPrenex parent.proof parent.existentialVariables
    | return none
  let bindings? := prenexed.variables.mapM fun variableName =>
    info.bindings.find? (·.existentialVariable == variableName)
  let some bindings := bindings? | return none
  let mut residual := prenexed.proof
  for binding in bindings do
    let some symbol := input.symbols.get? binding.symbol | return none
    let some (witness, nextResidual) ← BackendSkolemization.chooseWitness residual
      | return none
    -- `Replay` has introduced the local `let` named by `binding.symbol`.
    -- Checking definitional equality here verifies that this particular
    -- prenex witness, rather than an annotation position, supplies it.
    unless ← isDefEq witness symbol do return none
    residual := nextResidual
  BackendSkolemization.finish input.target residual

/-- Reuse a preprocessing parent when the displayed conclusion is unchanged.

This also handles identity nodes carrying an otherwise unsupported rule name.
The check is restricted to a single ordinary-formula parent; it is never a
shortcut around a clause-calculus certificate or an input-fact check. -/
def preprocessingIdentity (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  if parent.clauseForm then return none
  if ← isDefEq (← inferType parent.proof) input.target then
    trace[vampire.replay] "preprocessing {input.step.name}: parent already has the displayed result"
    return some parent.proof
  pure none

/-- Send a single-parent logical preprocessing inference to the independent
VampLean backend.  Its CNF handler searches the conjunction produced by
`cnfify` and validates literal permutations explicitly. -/
def preprocessWithVampLean (input : RuleInput) (rule : String) :
    MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  -- Vampire's logical preprocessing precedes the stored-clause phase.  A
  -- clause-form parent here would indicate a different certificate shape.
  if parent.clauseForm then return none
  let cnfCertificate? ← if rule == "cnf_transformation" &&
      input.step.inference?.any (·.hasCnfCertificate) then do
    let some certificate := input.step.inference?.bind Inference.cnfCertificate?
      | throwError "malformed CNF certificate for {input.step.name}"
    pure (some certificate)
  else pure none
  if cnfCertificate?.isNone then
    if let some proof ← preprocessingIdentity input then return some proof
  BackendPreprocessing.reconstruct {
    stepName := input.step.name
    rule
    target := input.target
    targetBinders := input.step.binders.map (·.name)
    parentBinders := parent.binders.map (·.name)
    parentProof := parent.proof
    cnfCertificate?
    cnfCandidates := parent.cnfCandidates
  }

/-- Prove `a → b` where `b` is `a` with some atoms weakened in the
direction of the implication: a disjunct added, a conjunct dropped, an atom
replaced by `True`/`False`, or an antecedent added.  The direction flips under
`¬` and in antecedents, so polarity is tracked implicitly.  `none` means the
two formulas are not related this way. -/
private partial def weakening (a b : Expr) : MetaM (Option Expr) := do
  let a := (← instantiateMVars a).consumeMData
  let b := (← instantiateMVars b).consumeMData
  if ← isDefEq a b then
    return some (← withLocalDeclD `h a fun h => mkLambdaFVars #[h] h)
  withLocalDeclD `h a fun h => do
    let some proof ← go h a b | return none
    some <$> mkLambdaFVars #[h] proof
where
  /-- A proof of `b` from `h : a`. -/
  go (h a b : Expr) : MetaM (Option Expr) := do
    if ← isDefEq a b then return some h
    if b.isConstOf ``True then return some (mkConst ``True.intro)
    if a.isConstOf ``False then return some (← mkAppOptM ``False.elim #[b, h])
    match a.not?, b.not? with
    | some a', some b' =>
      let some back ← weakening b' a' | return none
      return some (← withLocalDeclD `hb b' fun hb => do
        mkLambdaFVars #[hb] (mkApp h (mkApp back hb)))
    | _, _ => pure ()
    match a.and?, b.and? with
    | some (a₁, a₂), some (b₁, b₂) =>
      if let some p₁ ← go (← mkAppM ``And.left #[h]) a₁ b₁ then
        if let some p₂ ← go (← mkAppM ``And.right #[h]) a₂ b₂ then
          return some (← mkAppM ``And.intro #[p₁, p₂])
    | _, _ => pure ()
    if let some (a₁, a₂) := a.and? then
      if let some p ← go (← mkAppM ``And.left #[h]) a₁ b then return some p
      if let some p ← go (← mkAppM ``And.right #[h]) a₂ b then return some p
    match a.app2? ``Or, b.app2? ``Or with
    | some (a₁, a₂), some (b₁, b₂) =>
      if let some p₁ ← weakening a₁ b₁ then
        if let some p₂ ← weakening a₂ b₂ then
          return some (← mkAppM ``Or.imp #[p₁, p₂, h])
    | _, _ => pure ()
    if let some (a₁, a₂) := a.app2? ``Or then
      if let some p₁ ← weakening a₁ b then
        if let some p₂ ← weakening a₂ b then
          return some (← mkAppOptM ``Or.elim #[a₁, a₂, b, h, p₁, p₂])
    if let some (b₁, b₂) := b.app2? ``Or then
      if let some p ← go h a b₁ then return some (← mkAppOptM ``Or.inl #[b₁, b₂, p])
      if let some p ← go h a b₂ then return some (← mkAppOptM ``Or.inr #[b₁, b₂, p])
    -- Quantifiers over the same domain, and implications.
    if let .forallE n d₁ a' _ := a then
      if let .forallE _ d₂ b' _ := b then
        if !(← isProp d₁) then
          if ← isDefEq d₁ d₂ then
            if let some p ← withLocalDeclD n d₁ fun x => do
                let some p ← go (mkApp h x) (a'.instantiate1 x) (b'.instantiate1 x) | return none
                some <$> mkLambdaFVars #[x] p then
              return some p
        else if !a'.hasLooseBVars && !b'.hasLooseBVars then
          if let some back ← weakening d₂ d₁ then
            if let some p ← withLocalDeclD `x d₂ fun x => do
                let some p ← go (mkApp h (mkApp back x)) a' b' | return none
                some <$> mkLambdaFVars #[x] p then
              return some p
    -- An added antecedent, e.g. `B` weakened to `p → B` when `p := True`.
    if let .forallE _ d b' _ := b then
      if ← (pure !b'.hasLooseBVars <&&> isProp d) then
        if let some p ← withLocalDeclD `x d fun x => do
            let some p ← go h a b' | return none
            some <$> mkLambdaFVars #[x] p then
          return some p
    match a.app2? ``Exists, b.app2? ``Exists with
    | some (α, .lam n d₁ a' bi), some (_, .lam _ _ b' _) =>
      withLocalDeclD n d₁ fun x => do
        let ax := a'.instantiate1 x
        withLocalDeclD `hx ax fun hx => do
          let some p ← go hx ax (b'.instantiate1 x) | return none
          let intro ← mkAppOptM ``Exists.intro #[α, Expr.lam n d₁ b' bi, x, p]
          let body ← mkLambdaFVars #[x, hx] intro
          some <$> mkAppOptM ``Exists.elim #[α, Expr.lam n d₁ a' bi, b, h, body]
    | _, _ => return none

/-- Reconstruct `pure_predicate_removal`. A predicate occurring with a single
polarity is replaced by `False` (negative) or `True` (positive) and the result
simplified; the conclusion is therefore a weakening of the parent. -/
def purePredicateRemoval (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  if parent.clauseForm then return none
  let source ← Core.betaReduce (← instantiateMVars (← inferType parent.proof))
  let target ← Core.betaReduce (← instantiateMVars input.target)
  let some proof ← weakening source target | return none
  asExpectedType (mkApp proof parent.proof) input.target

/-- Reconstruct Vampire's `rectify`, which renames bound variables and may
also reorient equalities. -/
def rectify (input : RuleInput) : MetaM (Option Expr) := do
  unless input.sourceProof?.isNone && input.parents.size == 1 do return none
  let some parent := input.parents[0]? | return none
  if parent.clauseForm then return none
  BackendPreprocessing.symmMatch parent.proof input.target

end VampireHammer.Backend
