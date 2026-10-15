import VampireHammer.Export.Inhabitation

open Lean Meta Elab Tactic

private partial def withIrrelevantFunctions (type : Expr) (count : Nat)
    (functions : Array Expr) (k : Array Expr → MetaM Unit) : MetaM Unit := do
  if count == 0 then return ← k functions
  withLocalDeclD `irrelevant type fun function =>
    withIrrelevantFunctions type (count - 1) (functions.push function) k

-- More unrelated functions than the application budget must not hide the
-- one function that actually returns the missing domain.
elab "check_witness_filter " point:term ", " function:term : tactic => withMainContext do
  let point ← instantiateMVars (← Term.elabTerm point none)
  let function ← instantiateMVars (← Term.elabTerm function none)
  let target ← inferType (mkApp function point)
  let irrelevant ← mkArrow (← inferType point) (mkConst ``Nat)
  withIrrelevantFunctions irrelevant 72 #[] fun functions => do
    let witness? ← VampireHammer.Export.Internal.localDomainWitness target
      (functions ++ #[point, function]) (← IO.mkRef 64) 3
    let some witness := witness? | throwError "unrelated result types exhausted witness recovery"
    unless ← isDefEq (← inferType witness) target do throwError "recovered witness has the wrong type"
    checkWithKernel witness

example {α β : Type} (a : α) (f : α → β) : True := by
  check_witness_filter a, f
  trivial
