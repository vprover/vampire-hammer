import Auto.Tactic

/-! Quantifiers over subtypes, relativized to the base type.

Unfolding `Set.range (fun x : s => f x)` or `Set.image` of a coerced set leaves
`∃ x : ↥s, f ↑x = y`. The prover needs an inhabitant of every sort, and `↥s`
may be empty, so the subtype has no witness and the fact is lost. Relativized,
the same statement reads `∃ a, a ∈ s ∧ f a = y` over the base type, which is
the form the other facts about `s` take.

Each fact with a quantifier over a subtype is rewritten with `Subtype.forall`
and `Subtype.exists`, instantiated at its binders, and `exists_prop`. The rewrite is kept only when it removes
all such quantifiers and leaves no `⟨a, h⟩` of a bound element: a function on
the subtype, applied to its argument, still needs the subtype. -/

register_option vampire.relativizeSubtypes : Bool := {
  defValue := true
  descr := "Relativize quantifiers over subtypes to their base type"
}

namespace VampireHammer.SubtypeRelativization

open Lean Meta

/-- The subtype that `type` is by definition, such as `{x // x ∈ s}` for `↥s`. -/
private def asSubtype? (type : Expr) : MetaM (Option Expr) := do
  if type.isAppOf ``Subtype then return some type
  if type.hasLooseBVars then return none
  -- `↥s` is reducible; unfolding further would be expensive on large types.
  let type ← whnfR type
  return if type.isAppOf ``Subtype then some type else none

private def isSubtype (type : Expr) : MetaM Bool := return (← asSubtype? type).isSome

/-- Write subtype binders as `Subtype` applications, which the rewrite lemmas
match syntactically. A definitional change. -/
private def exposeSubtypes (e : Expr) : MetaM Expr :=
  Meta.transform e (pre := fun e => do
    match e with
    | .forallE name type body info =>
      if let some subtype ← asSubtype? type then
        if subtype != type then return .continue (some (.forallE name subtype body info))
    | .lam name type body info =>
      if let some subtype ← asSubtype? type then
        if subtype != type then return .continue (some (.lam name subtype body info))
    | _ =>
      if e.isAppOfArity ``Exists 2 then
        if let some subtype ← asSubtype? e.appFn!.appArg! then
          if subtype != e.appFn!.appArg! then
            let .const _ levels := e.getAppFn | return .continue e
            return .continue (some (mkApp2 (.const ``Exists levels) subtype e.appArg!))
    return .continue e)

/-- A `∀`, `fun` or `∃` binding an element of a subtype. -/
private def bindsSubtype (e : Expr) : MetaM Bool := do
  let found ← IO.mkRef false
  e.forEach' fun e => do
    if ← found.get then return false
    let binderType? := match e with
      | .forallE _ type _ _ | .lam _ type _ _ => some type
      | _ => if e.isAppOfArity ``Exists 2 then some e.appFn!.appArg! else none
    if let some type := binderType? then
      if ← isSubtype type then found.set true
    return true
  found.get

private def hasBoundConstructor (e : Expr) : Bool :=
  (e.find? fun e => e.isAppOfArity ``Subtype.mk 4 && e.hasLooseBVars).isSome

/-- `Subtype.forall` and `Subtype.exists` instantiated at each subtype binder
of `e`, closed over the enclosing binders. The rewrite lemmas cannot be left
to unification: a predicate such as `s : Set α` instantiates
`p : α → Prop` only up to unfolding `Set`, which `simp` does not do. -/
private def instances (e : Expr) : MetaM (Array Expr) := do
  let original ← getLCtx
  let found ← IO.mkRef (#[] : Array Expr)
  let close (proof : Expr) : MetaM Unit := do
    let binders := (← getLCtx).getFVars.filter fun x =>
      !original.contains x.fvarId! && proof.containsFVar x.fvarId!
    found.modify (·.push (← mkLambdaFVars binders proof))
  let _ ← Meta.transform e (pre := fun e => do
    match e with
    | .forallE name type body info =>
      if type.isAppOfArity ``Subtype 2 && !(← isProp type) then
        let .const _ [u] := type.getAppFn | return .continue e
        let q := Expr.lam name type body info
        close (mkApp3 (.const ``Subtype.forall [u]) type.appFn!.appArg! type.appArg! q)
    | _ =>
      if e.isAppOfArity ``Exists 2 then
        let type := e.appFn!.appArg!
        if type.isAppOfArity ``Subtype 2 then
          let .const _ [u] := type.getAppFn | return .continue e
          close (mkApp3 (.const ``Subtype.exists [u]) type.appFn!.appArg! type.appArg! e.appArg!)
    return .continue e)
  found.get

/-- The fact with its subtype quantifiers relativized, or the fact itself. -/
def relativize (lemma : Auto.Lemma) : MetaM Auto.Lemma := do
  unless vampire.relativizeSubtypes.get (← getOptions) do return lemma
  let saved ← saveState
  -- `try` does not catch the heartbeat limit.
  tryCatchRuntimeEx (Auto.Meta.withMaxHeartbeats 4000 do
    unless ← bindsSubtype lemma.type do return lemma
    let exposed ← exposeSubtypes lemma.type
    let mut theorems ← ({} : SimpTheorems).addConst ``exists_prop
    for proof in ← instances exposed do
      theorems ← theorems.add (.other `subtypeRelativization) #[] proof
    let context ← Simp.mkContext { maxSteps := 512 } #[theorems] (← getSimpCongrTheorems)
    let (result, _) ← simp exposed context
    let type ← instantiateMVars result.expr
    if type == lemma.type || type.hasMVar || (← bindsSubtype type) || hasBoundConstructor type then
      saved.restore
      return lemma
    let proof ← mkExpectedTypeHint lemma.proof exposed
    let proof ← match result.proof? with
      | some equality => mkEqMP equality proof
      | none => mkExpectedTypeHint proof type
    trace[vampire] "Relativized subtype quantifiers: {type}"
    return { lemma with proof, type })
    fun error => do
      if error.isInterrupt then throw error
      trace[vampire] "Subtype relativization failed: {error.toMessageData}"
      saved.restore
      return lemma

end VampireHammer.SubtypeRelativization
