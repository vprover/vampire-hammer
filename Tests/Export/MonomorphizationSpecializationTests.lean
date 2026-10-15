import Auto.Tactic

open Lean Meta Elab Command Auto.Monomorphization

private def mixedArguments (left : Nat) (right : Bool) {α : Type} (_ : α) : Nat :=
  if right then left else 0

private def orderedArguments (left right : Nat) {α : Type} (_ : α) : Nat :=
  left - right

private def interleavedArguments (left marker : Nat) (right : Bool) {α : Type} (_ : α) : Nat :=
  if right then left + marker else marker

private abbrev AliasedSignature := Nat → Bool → (α : Type) → α → Nat
private opaque aliasedArguments : AliasedSignature

private def specialize (name : Name) (indices : Array Nat) (arguments : Array Expr) : MetaM Expr := do
  let constant : ConstInst := {
    head := .const name #[]
    argsInst := arguments
    argsIdx := indices }
  let result ← constant.toExpr
  check result
  return result

-- The first two uninstantiated arguments have different types. Their order
-- must survive specialization of the later type parameter.
run_cmd liftTermElabM do
  let result ← specialize ``mixedArguments #[2] #[mkConst ``Unit]
  let applied := mkApp3 result (toExpr (3 : Nat)) (toExpr true) (mkConst ``Unit.unit)
  unless ← isDefEq applied (toExpr (3 : Nat)) do
    throwError "constant specialization reversed differently typed arguments"

-- Reversing equal-typed arguments can yield a well-typed but incorrect value.
run_cmd liftTermElabM do
  let result ← specialize ``orderedArguments #[2] #[mkConst ``Unit]
  let applied := mkApp3 result (toExpr (7 : Nat)) (toExpr (2 : Nat)) (mkConst ``Unit.unit)
  unless ← isDefEq applied (toExpr (5 : Nat)) do
    throwError "constant specialization changed the order of equal-typed arguments"

-- Instantiated values from the caller's context must not be captured by the
-- fresh binders created for the remaining arguments.
run_cmd liftTermElabM do
  withLocalDeclD `marker (mkConst ``Nat) fun marker => do
    let result ← specialize ``interleavedArguments #[1, 3] #[marker, mkConst ``Unit]
    let applied := mkApp3 result (toExpr (3 : Nat)) (toExpr true) (mkConst ``Unit.unit)
    let expected ← mkAppM ``Nat.add #[toExpr (3 : Nat), marker]
    unless ← isDefEq applied expected do
      throwError "constant specialization captured an instantiated argument"
    unless (collectFVars {} result).fvarIds.contains marker.fvarId! do
      throwError "constant specialization lost the caller's argument"

-- Function binders may be hidden behind a reducible type alias.
run_cmd liftTermElabM do
  let _ ← specialize ``aliasedArguments #[2] #[mkConst ``Unit]
