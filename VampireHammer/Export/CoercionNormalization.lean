import Auto.Tactic

/-! Coercions of bundled objects in a normal form, with their laws.

Bundled maps and subobjects reach the prover through coercions `⇑f x` and
`↑s`. The same value appears in many shapes (`⇑(g.comp f) x`, `g (f x)`,
`⇑f.toMonoidHom x`, …), and two bundled values with equal coercions are only
equal by extensionality. Lean's `simp` normal form settles both; this module
brings that normal form to the instantiated problem:

* every instantiated fact containing a coercion gets a copy whose coercion
  subterms are rewritten by the `@[simp]` set (Mathlib's `coe_comp`,
  `coe_mk`, `comp_apply`, …) and whose coercion instances are the canonical
  synthesized ones; other subterms are left alone, and the original fact is
  kept. With a constant codomain, monomorphization represents
  `@DFunLike.coe F α (fun _ => β) i` as one binary application symbol
  `F → α → β`; instances that are equal only by unfolding (`MonoidHom` maps
  coerced through `MonoidHomClass` or directly) would split it into several;
* every coercion `@DFunLike.coe F α (fun _ => β) _` or `@SetLike.coe A B _` of
  the problem gets its extensionality (`f = g ↔ ∀ x, f x = g x`) and the
  injectivity of the coercion.

Mathlib is not imported here: its coercions and laws are found by name and are
skipped when absent. The new facts carry checked proofs and are optional. -/

register_option vampire.normalizeCoercions : Bool := {
  defValue := true
  descr := "Add copies of instantiated facts whose coercions are in simp normal form"
}

register_option vampire.coercionLaws : Bool := {
  defValue := true
  descr := "Add extensionality and coercion injectivity for each bundled coercion of the problem"
}

namespace VampireHammer.Export.CoercionNormalization

open Lean Meta

def labelPrefix : String := "coercion normal form "
def lawLabelPrefix : String := "coercion law "

private def maxCopies : Nat := 64
private def maxCoercions : Nat := 16

/-- Heads rewritten by the normalization: the coercions and the plumbing
that their simp lemmas produce (`⇑g ∘ ⇑f`). -/
private def rewrittenHeads : Array Name :=
  #[`DFunLike.coe, `SetLike.coe, ``Function.comp, ``id]

/-- Rewrite a coercion only of a constructed bundled value (`⇑(g.comp f)`,
`⇑(MulHom.single i)`, `⇑⟨f, h⟩`). A coercion of a variable is where class laws
such as `map_mul` apply; rewriting with them would turn those very laws,
which are facts of the problem, into tautologies. -/
private def isRewritten (e : Expr) : Bool :=
  match e.getAppFn with
  | .const name _ =>
    if name == `DFunLike.coe || name == `SetLike.coe then
      let bundled := e.getAppArgs[if name == `DFunLike.coe then 4 else 3]?
      bundled.any fun value => value.getAppFn.isConst
    else rewrittenHeads.contains name
  | _ => false

/-- `∀ xs, a = a`, `∀ xs, a ↔ a` or `∀ xs, True`. -/
private def isTautology (type : Expr) : MetaM Bool :=
  forallTelescope type fun _ body => do
    if body.isTrue then return true
    if let some (_, lhs, rhs) := body.eq? then return lhs == rhs
    if let some (lhs, rhs) := body.iff? then return lhs == rhs
    return false

private def mentionsCoercion (e : Expr) : Bool :=
  (e.find? fun e => e.isConstOf `DFunLike.coe || e.isConstOf `SetLike.coe).isSome

/-- Replace the instance of each coercion by the synthesized one when they are
definitionally equal, so that each bundled type has one application symbol. -/
private def canonicalizeInstances (type : Expr) : MetaM Expr :=
  Meta.transform type (post := fun e => do
    let arity := if e.isAppOf `DFunLike.coe then 4 else if e.isAppOf `SetLike.coe then 3 else 0
    if arity == 0 || e.getAppNumArgs < arity then return .done e
    let arguments := e.getAppArgs
    let current := arguments[arity - 1]!
    try
      let some canonical ← synthInstance? (← inferType current) | return .done e
      if canonical == current then return .done e
      unless ← withTransparency .instances <| withNewMCtxDepth <| isDefEq canonical current do
        return .done e
      return .done (mkAppN e.getAppFn (arguments.set! (arity - 1) canonical))
    catch _ => return .done e)

/-- The fact with its coercion subterms in simp normal form, or `none`. -/
private def normalize (context : Simp.Context) (fact : Auto.Lemma) : MetaM (Option Auto.Lemma) := do
  let defaults := Simp.mkDefaultMethodsCore {}
  let methods := { defaults with
    pre := fun e => if isRewritten e then Simp.rewritePre (rflOnly := false) e else return .continue
    post := fun e => if isRewritten e then Simp.rewritePost (rflOnly := false) e else return .done { expr := e } }
  let saved ← saveState
  -- `try` does not catch the heartbeat limit.
  tryCatchRuntimeEx (do
    let (result, _) ← Auto.Meta.withMaxHeartbeats 8000 <| Simp.main fact.type context (methods := methods)
    let normal ← Auto.Meta.withMaxHeartbeats 8000 <| canonicalizeInstances result.expr
    if normal == fact.type || normal.hasMVar || (← isTautology normal) then
      saved.restore
      return none
    let proof ← match result.proof? with
      | some equality => mkEqMP equality fact.proof
      | none => pure fact.proof
    -- Canonical instances are definitionally equal to the replaced ones.
    let proof ← mkExpectedTypeHint proof normal
    return some ⟨⟨proof, normal, .leaf s!"{labelPrefix}of {fact.deriv}"⟩, #[]⟩)
    fun error => do
      if error.isInterrupt then throw error
      saved.restore
      return none

/-- Copies of the coercion-carrying facts in simp normal form. -/
def normalizeFacts (facts : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  let candidates := facts.filter fun fact => fact.params.isEmpty && mentionsCoercion fact.type
  if candidates.isEmpty then return #[]
  let context ← Simp.mkContext { maxSteps := 512 } #[← getSimpTheorems] (← getSimpCongrTheorems)
  let mut copies := #[]
  for fact in candidates do
    if copies.size >= maxCopies then break
    if let some copy ← normalize context fact then
      trace[vampire] "Coercion normal form: {copy.type}"
      copies := copies.push copy
  return copies

/-- Closed coercions applied in the facts, as the partial applications
`@DFunLike.coe F α (fun _ => β) i` (with a constant codomain) and
`@SetLike.coe A B i`. -/
private def coercions (facts : Array Auto.Lemma) : MetaM (Array Expr) := do
  let original ← getLCtx
  let found ← IO.mkRef (#[] : Array Expr)
  for fact in facts do
    let _ ← Meta.transform fact.type (pre := fun e => do
      let arity := if e.isAppOf `DFunLike.coe then 4 else if e.isAppOf `SetLike.coe then 3 else 0
      if arity == 0 || e.getAppNumArgs < arity then return .continue e
      let coercion := mkAppN e.getAppFn (e.getAppArgs.extract 0 arity)
      if coercion.hasAnyFVar (fun id => !original.contains id) || coercion.hasMVar then
        return .continue e
      if arity == 4 then
        let .lam _ _ codomain _ := e.getAppArgs[2]! | return .continue e
        if codomain.hasLooseBVars then return .continue e
      found.modify fun found =>
        if found.contains coercion || found.size >= maxCoercions then found else found.push coercion
      return .continue e)
  found.get

/-- `∀ f g, f = g ↔ …` from an extensionality lemma `ext_iff {f g}`, and
`∀ f g, ⇑f = ⇑g → f = g` from `coe_injective`, for one coercion. -/
private def laws (coercion : Expr) : MetaM (Array Auto.Lemma) := do
  let env ← getEnv
  let arguments := coercion.getAppArgs
  let (extName, injectiveName) := if coercion.isAppOf `DFunLike.coe then
    (`DFunLike.ext_iff, `DFunLike.coe_injective) else (`SetLike.ext_iff, `SetLike.coe_injective)
  let bundled := arguments[0]!
  withLocalDeclD `f bundled fun f => withLocalDeclD `g bundled fun g => do
    let mut found := #[]
    if env.contains extName then
      try
        let proof ← mkAppOptM extName ((arguments.map some) ++ #[some f, some g])
        let type ← inferType proof
        found := found.push ⟨⟨← mkLambdaFVars #[f, g] proof, ← mkForallFVars #[f, g] type,
          .leaf s!"{lawLabelPrefix}extensionality of {coercion}"⟩, #[]⟩
      catch _ => pure ()
    if env.contains injectiveName then
      try
        let premise ← mkEq (mkApp coercion f) (mkApp coercion g)
        let statement ← mkArrow premise (← mkEq f g)
        let injective ← mkAppOptM injectiveName (arguments.map some)
        let proof ← withLocalDeclD `h premise fun h => do
          let proof := mkAppN injective #[f, g, h]
          check proof
          mkLambdaFVars #[h] proof
        found := found.push ⟨⟨← mkLambdaFVars #[f, g] (← mkExpectedTypeHint proof statement),
          ← mkForallFVars #[f, g] statement,
          .leaf s!"{lawLabelPrefix}injectivity of {coercion}"⟩, #[]⟩
      catch _ => pure ()
    return found

/-- Extensionality and coercion injectivity for the coercions of the facts. -/
def coercionLaws (facts : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  let mut found := #[]
  for coercion in ← coercions facts do
    for law in ← laws coercion do
      trace[vampire] "Coercion law: {law.type}"
      found := found.push law
  return found

/-- The extension passed to `Auto.Monomorphization.monomorphize`. -/
def extend (facts : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  let options ← getOptions
  let normalized ← if vampire.normalizeCoercions.get options then normalizeFacts facts else pure #[]
  let laws ← if vampire.coercionLaws.get options then coercionLaws facts else pure #[]
  return normalized ++ laws

end VampireHammer.Export.CoercionNormalization
