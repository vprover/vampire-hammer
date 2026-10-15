import Auto.Tactic

open Lean Meta Elab Command Auto.Embedding.Lam

private abbrev AliasedType := Type

private def reifySort (type : Expr) : MetaM (LamSort × Array (Expr × Level)) := do
  let action : Auto.LamReif.ReifM (LamSort × Array (Expr × Level)) := do
    let sort ← Auto.LamReif.newTypeExpr type
    return (sort, ← Auto.LamReif.getTyVal)
  (action.run' {u := .succ .zero}).run' {declName? := none}

-- The type of a type variable can itself be a reducible sort alias.
run_cmd liftTermElabM do
  withLocalDeclD `α (mkConst ``AliasedType) fun type => do
    let (sort, values) ← reifySort type
    unless sort == .atom 0 && values == #[(type, .succ .zero)] do
      throwError "reification failed to preserve an aliased type's valuation and universe"

-- outParam is an ordinary reducible wrapper; no name-specific rule is needed.
run_cmd liftTermElabM do
  let wrapped ← mkAppM ``outParam #[mkSort (.succ .zero)]
  withLocalDeclD `α wrapped fun type => do
    let (sort, values) ← reifySort type
    unless sort == .atom 0 && values == #[(type, .succ .zero)] do
      throwError "reification failed to reduce a wrapped sort"

-- Reducing the inferred type must not turn ordinary data into a type.
run_cmd liftTermElabM do
  let rejected ← try
    let _ ← reifySort (toExpr (0 : Nat))
    pure false
  catch _ => pure true
  unless rejected do throwError "reification accepted a non-type as a domain"
