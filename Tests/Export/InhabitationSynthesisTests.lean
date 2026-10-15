import Auto.Tactic

open Lean Meta Elab Command

private def checkWitness (type : Expr) : MetaM Unit := do
  let some witness ← Auto.Meta.trySynthInhabited type
    | throwError "failed to synthesize an existing witness for {type}"
  unless ← isDefEq (← inferType witness) type do
    throwError "inhabitation synthesis returned an incorrectly typed witness"
  unless ← isTypeCorrect witness do
    throwError "inhabitation synthesis returned an ill-typed witness"

-- These types are not themselves classes. A failed direct class search must
-- still try their Inhabited instances.
run_cmd liftTermElabM do
  checkWitness (mkConst ``Nat)
  checkWitness (mkConst ``Unit)
  checkWitness (mkSort .zero)
  checkWitness (mkForall `x .default (mkConst ``Empty) (mkConst ``Nat))

inductive ChoiceDomain where
  | point

instance : Nonempty ChoiceDomain := ⟨ChoiceDomain.point⟩

-- Nonempty must work even when there is no Inhabited instance.
run_cmd liftTermElabM do
  checkWitness (mkConst ``ChoiceDomain)

class WitnessClass where
  value : Nat

instance : WitnessClass := ⟨0⟩

-- Preserve synthesis of the type itself when it is a class.
run_cmd liftTermElabM do
  checkWitness (mkConst ``WitnessClass)

-- None of the preceding witnesses can establish that an empty domain has
-- an element, even though functions from Empty to Nat are inhabited.
run_cmd liftTermElabM do
  unless (← Auto.Meta.trySynthInhabited (mkConst ``Empty)).isNone do
    throwError "inhabitation synthesis populated an empty domain"
