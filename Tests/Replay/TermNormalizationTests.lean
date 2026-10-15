import VampireHammer.Replay.Decode.Context

open VampireHammer.Replay VampireHammer.Replay.Internal VampireHammer.Replay.Decode.Internal
open Auto.Embedding.Lam

#eval show IO Unit from do
  let p := LamTerm.atom 0
  let q := LamTerm.atom 1
  let r := LamTerm.atom 2
  let normalize := fun term => (normalizeSourceOr { term, sort := .base .prop }).term
  unless normalize (.mkOr (.mkOr p q) r) == .mkOr p (.mkOr q r) do
    throw <| IO.userError "source disjunction did not become right-associated"
  -- Do not reorder, simplify, or deduplicate source literals.
  let duplicates := .mkOr (.mkOr p (.base .falseE)) p
  unless flattenOr (normalize duplicates) == [p, .base .falseE, p] do
    throw <| IO.userError "source normalization changed literal occurrences"
  let quantified := LamTerm.mkForallEF (.atom 0) (.mkOr (.mkOr (.bvar 0) q) r)
  let expected := LamTerm.mkForallEF (.atom 0) (.mkOr (.bvar 0) (.mkOr q r))
  unless normalize quantified == expected do
    throw <| IO.userError "source normalization missed a disjunction under a binder"
  let nested := LamTerm.mkAnd (.mkOr (.mkOr p q) r) (.mkOr q p)
  let expected := LamTerm.mkAnd (.mkOr p (.mkOr q r)) (.mkOr q p)
  unless normalize nested == expected do
    throw <| IO.userError "source normalization changed another connective's grouping"
  unless rightAssociate? LamTerm.mkOr [] == none && rightAssociate? LamTerm.mkOr [p] == some p do
    throw <| IO.userError "empty or singleton connective sequence changed"
  let literals := (List.range 6000).map LamTerm.atom
  let chain := literals.foldl LamTerm.mkOr r
  unless flattenOr (normalize chain) == r :: literals do
    throw <| IO.userError "long source disjunction lost its occurrence order"
  let andChain := literals.foldl LamTerm.mkAnd r
  unless flattenAnd andChain == r :: literals do
    throw <| IO.userError "long conjunction lost its occurrence order"
  IO.println "Term normalization: nested binders, occurrence order, and 6000-literal chains passed"
