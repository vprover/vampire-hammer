import Auto.Translation.Inductive

open Lean Meta Elab Command

-- These inferred types are inspected after source normalization. Their lets
-- must be reduced by the collector rather than rejected as invalid input.
elab "check_inductive_lets" : command => liftTermElabM do
  let type := mkSort (.succ .zero)
  let nat := mkConst ``Nat
  let bool := mkConst ``Bool
  let simple := Expr.letE `T type nat (.bvar 0) false
  let nested := Expr.letE `A type nat
    (.letE `B type bool (.forallE `x (.bvar 1) (.bvar 1) .default) false) false
  for (expression, expected) in #[(simple, #[``Nat]), (nested, #[``Nat, ``Bool])] do
    let collected ← Auto.collectExprsSimpleInduct #[expression]
    for name in expected do
      unless collected.any (·.any (·.name == name)) do
        throwError "collector missed {name} beneath a let"

check_inductive_lets

-- These expressions arrive from inferred signatures or constructors rather
-- than from a normalized source statement. Projection parameters must be
-- recovered from the actual value, and metadata must remain transparent.
elab "check_inductive_projections" : command => liftTermElabM do
  let pairType ← mkAppM ``Prod #[mkConst ``Nat, mkConst ``Nat]
  withLocalDeclD `pair pairType fun pair => do
    let projection := Expr.proj ``Prod 0 pair
    let metadata := Expr.mdata {} projection
    let nested := Expr.letE `pair pairType pair (.proj ``Prod 1 (.bvar 0)) false
    for expression in #[projection, metadata, nested] do
      let collected ← Auto.collectExprsSimpleInduct #[expression]
      unless collected.any (·.any (·.name == ``Nat)) do
        throwError "collector missed the projection's Nat parameter"

check_inductive_projections
