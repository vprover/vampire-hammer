import VampireHammer.Replay.Decode.Context

open VampireHammer VampireHammer.Replay VampireHammer.Replay.Decode.Internal
open Auto.Embedding.Lam

#eval show IO Unit from do
  let prop := LamSort.base .prop
  let problem : TFF.Problem := {
    text := "", facts := #[], sorts := #[("s", .atom 0), ("s", .atom 1)],
    symbols := #[("p", .atom 0, prop), ("p", .atom 1, prop)] }
  let context : Context := { problem, derivedSymbols := #[
    { name := "p", term := .etom 0, sort := prop, kind := .predicateDefinition },
    { name := "fresh", term := .etom 1, sort := prop, kind := .avatarDefinition }] }
  unless (← IO.ofExcept (lookupSort "s" |>.run context)) == .atom 0 do
    throw <| IO.userError "sort lookup lost first-declaration priority"
  unless (← IO.ofExcept (lookupSymbol "p" |>.run context)) == (.atom 0, prop) do
    throw <| IO.userError "proof-local symbol shadowed an exporter symbol"
  let boundContext := { context with bound := [("X", .atom 0)] }
  unless (← IO.ofExcept (lookupSymbol "fresh" |>.run boundContext)) == (.etom 1, prop) do
    throw <| IO.userError "changing binder scope lost the proof-local symbol index"
  for diagnostic in [lookupSort "missing" |>.run context |>.map (fun _ => ()),
      lookupSymbol "missing" |>.run context |>.map (fun _ => ())] do
    match diagnostic with
    | .ok _ => throw <| IO.userError "invented an undeclared sort or symbol"
    | .error message => unless message.contains "missing" do
        throw <| IO.userError s!"lost the missing name in a lookup diagnostic: {message}"
  IO.println "Decoder lookup: declaration priority, binder scopes, and missing names passed"
