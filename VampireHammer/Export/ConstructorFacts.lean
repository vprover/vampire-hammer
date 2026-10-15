import Auto.Tactic

/-! Checked injectivity and distinctness laws for constructor symbols occurring
in the source. These use the inductive's no-confusion principle, not named
injectivity lemmas. -/

namespace VampireHammer.Export.ConstructorFacts

open Lean Meta

def labelPrefix : String := "constructor law "

/-- Generate one implication per independent data field. Dependent fields and
proof fields and type-valued fields are left to the existing encoding rather
than approximated. -/
private def injectivityLaws (constructor : Expr) : MetaM (Array Auto.Lemma) := do
  let type ← inferType constructor
  forallTelescopeReducing type fun left _ => do
    if left.isEmpty || left.size > 8 then return #[]
    -- Reusing the function telescope is only valid for independent fields.
    for field in left do
      let fieldType ← inferType field
      if fieldType.hasAnyFVar (fun id => left.any (·.fvarId! == id)) then
        return #[]
      -- Quantifying over types, including type-valued function fields, would
      -- introduce bound type arguments that Auto cannot monomorphize.
      if ← forallTelescopeReducing fieldType fun _ result => pure result.isSort then
        return #[]
    forallTelescopeReducing type fun right _ => do
      let equality ← mkEq (mkAppN constructor left) (mkAppN constructor right)
      let mut result := #[]
      for i in [:left.size] do
        if ← isProof left[i]! then continue
        let conclusion ← mkEq left[i]! right[i]!
        let law ← withLocalDeclD `sameConstructor equality fun h =>
          mkForallFVars (left ++ right ++ #[h]) conclusion
        let saved ← saveState
        try
          let goal ← mkFreshExprMVar law .syntheticOpaque
          let (variables, body) ← goal.mvarId!.introN (2 * left.size + 1)
          match ← Lean.Meta.injection body variables.back! with
          | .solved => pure ()
          | .subgoal remaining _ _ => remaining.assumption
          let proof ← instantiateMVars goal
          if ← (pure proof.hasMVar <||> (do return !(← isTypeCorrect proof))) then
            throwError "incomplete constructor injectivity certificate"
          result := result.push ⟨⟨proof, law, .leaf s!"{labelPrefix}{constructor} field {i}"⟩, #[]⟩
        catch _ => saved.restore
      return result

/-- Whether a field quantifies over types. Auto cannot monomorphize the bound
type arguments such a law would introduce. -/
private def isTypeValued (field : Expr) : MetaM Bool := do
  forallTelescopeReducing (← inferType field) fun _ result => pure result.isSort

/-- `∀ fields, left fields ≠ right fields` for two different constructors with
the same parameters, closed by no-confusion. Without these laws distinct
constructors are unrelated TF0 constants, and the prover may identify them. -/
private def distinctnessLaw (left right : Expr) : MetaM (Option Auto.Lemma) := do
  forallTelescopeReducing (← inferType left) fun leftFields _ => do
  forallTelescopeReducing (← inferType right) fun rightFields _ => do
    let fields := leftFields ++ rightFields
    if fields.size > 8 then return none
    if ← fields.anyM isTypeValued then return none
    let difference := mkNot (← mkEq (mkAppN left leftFields) (mkAppN right rightFields))
    let law ← mkForallFVars fields difference
    let goal ← mkFreshExprMVar law .syntheticOpaque
    let (variables, body) ← goal.mvarId!.introN (fields.size + 1)
    let .solved ← Lean.Meta.injection body variables.back!
      | throwError "constructors {left} and {right} were not separated by no-confusion"
    let proof ← instantiateMVars goal
    if ← (pure proof.hasMVar <||> (do return !(← isTypeCorrect proof))) then
      throwError "incomplete constructor distinctness certificate"
    return some ⟨⟨proof, law, .leaf s!"{labelPrefix}{left} ≠ {right}"⟩, #[]⟩

/-- Pairwise distinctness of all constructors of an inductive instance, given
as `(inductive name, universe levels, parameters)`. Indexed families are
skipped: their constructors can target different index values and types. -/
private def distinctnessLaws (family : Name × List Level × Array Expr) :
    MetaM (Array Auto.Lemma) := do
  let (name, levels, parameters) := family
  let some (.inductInfo info) := (← getEnv).find? name | return #[]
  if info.numIndices != 0 || info.ctors.length > 8 then return #[]
  let constructors := info.ctors.toArray.map fun ctor => mkAppN (mkConst ctor levels) parameters
  let mut laws := #[]
  for i in [:constructors.size] do
    for j in [i + 1:constructors.size] do
      let saved ← saveState
      try
        if let some law ← distinctnessLaw constructors[i]! constructors[j]! then
          laws := laws.push law
      catch _ => saved.restore
  return laws

/-- Inspect only constructor applications present in the requested source.
Parameters must belong to the caller's context: binders opened temporarily
while walking a formula cannot escape into an exported law. -/
def collect (sources : Array Auto.Lemma) : MetaM (Array Auto.Lemma) := do
  let original ← getLCtx
  let mut constructors : Array Expr := #[]
  for source in sources do
    let sourceType ← instantiateMVars source.type
    let scan : StateRefT (Array Expr) MetaM Expr := Meta.transform sourceType (post := fun expression => do
      if (← get).size >= 16 then return .done expression
      let .const name _ := expression.getAppFn | return .done expression
      let some (.ctorInfo info) := (← getEnv).find? name | return .done expression
      let args := expression.getAppArgs
      unless args.size == info.numParams + info.numFields do return .done expression
      let constructor := mkAppN expression.getAppFn (args.extract 0 info.numParams)
      unless (collectFVars {} constructor).fvarIds.all original.contains do
        return .done expression
      modify fun (found : Array Expr) =>
        if found.contains constructor then found else found.push constructor
      return .done expression)
    let (_, found) ← scan.run #[]
    for constructor in found do
      if constructors.size >= 16 then break
      unless constructors.contains constructor do constructors := constructors.push constructor
  let mut laws := #[]
  let mut families : Array (Name × List Level × Array Expr) := #[]
  for constructor in constructors do
    let saved ← saveState
    try laws := laws ++ (← injectivityLaws constructor)
    catch _ => saved.restore
    let .const name levels := constructor.getAppFn | continue
    let some (.ctorInfo info) := (← getEnv).find? name | continue
    let family := (info.induct, levels, constructor.getAppArgs)
    if families.size < 4 && !families.contains family then families := families.push family
  for family in families do
    laws := laws ++ (← distinctnessLaws family)
  return laws

end VampireHammer.Export.ConstructorFacts
