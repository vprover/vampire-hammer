import VampireHammer.SourceNormalization
import Lean.Meta.Tactic.Grind.EMatchTheorem
import Lean.Meta.Tactic.Grind.Attr

open Lean Meta

register_option vampire.attributeLemmas : Bool := {
  defValue := true
  descr := "Select relevant simp and grind theorem instances for the TF0 problem"
}
register_option vampire.attributeLemmaLimit : Nat := {
  defValue := 16
  descr := "Maximum automatically selected simp/grind theorem instances"
}

register_option vampire.attributeLemmaRounds : Nat := {
  defValue := 1
  descr := "Bounded rounds of premise discovery at newly exposed terms (at most four)"
}
register_option vampire.definitionLemmas : Bool := {
  defValue := false
  descr := "Include compiler-generated defining equations in bounded premise discovery"
}

namespace VampireHammer.AttributeLemmas

initialize registerTraceClass `vampire.premises

def labelPrefix := "attribute lemma "

private def logical (name : Name) : Bool :=
  #[`Eq, `HEq, `And, `Or, `Not, `Iff, `Exists, `True, `False].contains name

/-- Reject unrelated indexed candidates before full unification. Compare
reducible heads too, since the index canonicalizes notation and aliases. -/
def matchingHead (pattern anchor : Expr) : MetaM Bool := do
  let same (left right : Expr) : Bool :=
    match left.getAppFn, right.getAppFn with
    | .const left _, .const right _ => left == right
    | .fvar left, .fvar right => left == right
    | _, _ => false
  if same pattern anchor then return true
  let pattern ← withTransparency .reducible <| whnf pattern
  let anchor ← withTransparency .reducible <| whnf anchor
  return same pattern anchor

private partial def anchors (e : Expr) (result : Array Expr := #[]) : MetaM (Array Expr) := do
  let mut result := result
  if result.size >= 64 then return result
  if !e.hasLooseBVars && e.isApp then
    if let .const name _ := e.getAppFn then
      if !logical name && !result.contains e then result := result.push e
  match e with
  | .app .. =>
    -- Index maximal applications, not every curried prefix. Type, proof and
    -- instance arguments encode the elaborated implementation rather than
    -- the mathematical terms that should guide premise selection.
    let head := e.getAppFn
    unless head.isConst || head.isFVar do result ← anchors head result
    let mut functionType ← inferType head
    for argument in e.getAppArgs do
      let .forallE _ _ body binder ← whnf functionType | break
      functionType := body.instantiate1 argument
      if binder == .instImplicit then continue
      let type ← inferType argument
      if type.isSort && type != mkSort .zero then continue
      if ← isProp type then continue
      result ← anchors argument result
    return result
  | .forallE _ t b _ | .lam _ t b _ =>
    -- Search indexed theorems at symbolic binder arguments. Specialization
    -- closes any unresolved scalar arguments universally before accepting a
    -- fact, so these metavariables never escape into the selected proof.
    result ← anchors t result
    let argument ← mkFreshExprMVar t
    anchors (b.instantiate1 argument) result
  | .letE _ t v b _ => anchors (b.instantiate1 v) (← anchors v (← anchors t result))
  | .mdata _ b | .proj _ _ b => anchors b result
  | _ => return result

def domainHeads (expression : Expr) : MetaM (Std.HashSet Name) := do
  let names ← IO.mkRef ({} : Std.HashSet Name)
  let _ ← Meta.transform expression (pre := fun e => do
    let type ← withTransparency .default <| whnf (← inferType e)
    unless ← (pure (type.isSort || type.isForall) <||> isProp type <||>
        (do return (← isClass? type).isSome)) do
      if let .const name _ := type.getAppFn then names.modify (·.insert name)
    return .continue e)
  names.get

/-- Close leftover scalar/proof parameters universally. Types, instances,
functions and dependent data must have been determined by the matched term. -/
partial def closeParameters (parameters : Array Expr) (index : Nat)
    (proof : Expr) (locals : Array Expr := #[]) : MetaM (Option Expr) := do
  if index == parameters.size then
    let proof ← mkLambdaFVars locals (← instantiateMVars proof)
    if proof.hasMVar then return none
    return some proof
  let parameter ← instantiateMVars parameters[index]!
  unless parameter.isMVar do
    return ← closeParameters parameters (index + 1) proof locals
  let type ← instantiateMVars (← inferType parameter)
  if type.hasMVar then return none
  if (← isClass? type).isSome then
    let .some instanceProof ← trySynthInstance type | return none
    parameter.mvarId!.assign instanceProof
    return ← closeParameters parameters (index + 1) proof locals
  let reduced ← withTransparency .default <| whnf type
  if reduced.isSort then return none
  unless ← isProp type do
    if reduced.isForall || type.hasAnyFVar (fun id => locals.any (·.fvarId! == id)) then
      return none
  withLocalDeclD `vampireParameter type fun value => do
    parameter.mvarId!.assign value
    closeParameters parameters (index + 1) proof (locals.push value)

private def specialize (name : Name) (anchor : Expr) (simpInverse? : Option Bool)
    (grindPatterns : Array Expr) :
    MetaM (Option Auto.Lemma) := do
  let saved ← saveState
  try
    let proof ← mkConstWithFreshMVarLevels name
    let (parameters, _, body) ← forallMetaTelescopeReducing (← inferType proof)
    let proof := mkAppN proof parameters
    let mut patterns := #[]
    if let some inverse := simpInverse? then
      let root := if let some (_, lhs, rhs) := body.eq? then
          if inverse then rhs else lhs
        else if let some (lhs, rhs) := body.iff? then
          if inverse then rhs else lhs
        else body
      -- The index canonicalizes reducible aliases. A theorem's source head
      -- can therefore differ from the indexed anchor's head; defeq matching
      -- below must decide applicability rather than a literal name check.
      if ← matchingHead root anchor then patterns := #[root]
    else
      let info ← getConstInfo name
      patterns := grindPatterns.map fun pattern =>
        (pattern.instantiateLevelParams info.levelParams proof.getAppFn.constLevels!).instantiateRev parameters
    let patternState ← saveState
    for pattern in patterns do
      patternState.restore
      if ← withTransparency .reducible <| isDefEq pattern anchor then
        if let some proof ← closeParameters parameters 0 proof then
          let type ← inferType proof
          let lemma : Auto.Lemma := ⟨⟨proof, type, .leaf s!"{labelPrefix}{name}"⟩, #[]⟩
          let lemma ← Auto.unfoldConstAndPreprocessLemma #[] lemma
          let lemma ← SourceNormalization.normalizeLemma lemma
          saved.restore
          return some lemma
    saved.restore
    return none
  catch _ =>
    saved.restore
    return none

/-- Consult attribute indexes without scanning the environment or loading
whole namespaces. Instantiate a bounded set at existing source terms. -/
def collect (lemmas : Array Auto.Lemma) (exclude? : Option Name := none) : MetaM (Array Auto.Lemma) := do
  let options ← getOptions
  unless vampire.attributeLemmas.get options do return #[]
  let limit := vampire.attributeLemmaLimit.get options
  if limit == 0 then return #[]
  -- The source datatypes are only needed to vet a matched candidate, which
  -- most problems never produce; compute them on first use.
  let mut knownDomains? : Option (Std.HashSet Name) := none
  let simpTheorems ← simpExtension.getTheorems
  let grindTheorems ← match ← Grind.getExtension? `grind with
    | some extension => extension.getEMatchTheorems
    | none => pure {}
  let mut result := #[]
  let mut seen : Std.HashSet (Name × Expr) := {}
  let mut frontier := lemmas
  let mut searched : Std.HashSet Expr := {}
  let rounds := min 4 (max 1 (vampire.attributeLemmaRounds.get options))
  for round in [:rounds] do
    let mut terms := #[]
    for lemma in frontier do
      let sourceType ← instantiateMVars (← inferType lemma.proof)
      terms ← anchors sourceType terms
      terms ← anchors lemma.type terms
    let mut attempts := 0
    let mut next := #[]
    for term in terms do
      if searched.contains term then continue
      searched := searched.insert term
      let mut names : Array (Name × Option Bool × Array Expr) := #[]
      for thm in (← simpTheorems.pre.getMatch term) ++ (← simpTheorems.post.getMatch term) do
        if simpTheorems.erased.contains thm.origin then continue
        if let .decl name _ inverse := thm.origin then names := names.push (name, some inverse, #[])
      if let some (theorems, _) := grindTheorems.retrieve? term.getAppFn.constName! then
        for thm in theorems do
          if grindTheorems.isErased thm.origin then continue
          if let .decl name := thm.origin then names := names.push (name, none, thm.patterns.toArray)
      if vampire.definitionLemmas.get options then
        if let some (.defnInfo _) := (← getEnv).find? term.getAppFn.constName! then
          if let some equations ← getEqnsFor? term.getAppFn.constName! then
            for equation in equations do names := names.push (equation, some false, #[])
      let mut termAttempts := 0
      for (name, inverse?, grindPatterns) in names do
        if exclude? == some name || seen.contains (name, term) then continue
        if result.size >= limit then return result
        if attempts >= 128 then break
        -- Coarse grind buckets for common predicates can contain hundreds of
        -- candidates. They must not consume the budget for every later term.
        if termAttempts >= 16 then break
        attempts := attempts + 1
        termAttempts := termAttempts + 1
        if let some lemma ← specialize name term inverse? grindPatterns then
          seen := seen.insert (name, term)
          -- Do not introduce additional datatype theories incidentally. Their
          -- inhabitation and interpretation were not part of the source problem.
          let knownDomains ← match knownDomains? with
            | some known => pure known
            | none => do
              let mut known : Std.HashSet Name := {}
              for source in lemmas do
                for name in (← domainHeads source.type).toArray do
                  known := known.insert name
              pure known
          knownDomains? := some knownDomains
          unless (← domainHeads lemma.type).toArray.all knownDomains.contains do continue
          unless result.any (·.type == lemma.type) do
            trace[vampire.premises] "Selected {name} for {term}"
            result := result.push lemma
            next := next.push lemma
    -- Lowering can expose operations hidden behind a higher-order wrapper.
    -- Retain the original first round and discover from these operations and
    -- selected theorem conclusions only in subsequent bounded rounds.
    -- Only a following round consumes `next`.
    if round + 1 == rounds then break
    if round == 0 then
      for lemma in lemmas do
        let normalized ← SourceNormalization.normalizeLemma lemma
        if normalized.type != lemma.type then next := next.push normalized
    if next.isEmpty then break
    frontier := next
  return result

end VampireHammer.AttributeLemmas
