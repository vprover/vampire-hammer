import VampireHammer.Replay.Decode
import VampireHammer.TSTP

open VampireHammer VampireHammer.Backend VampireHammer.Replay.Decode.Internal
open Auto.Embedding.Lam

private def node (name : String) (parents : Array String := #[]) : Step := {
  name, parents := parents.map fun name => { name }
  formula := .base .trueE, binders := #[], sourceFact? := none,
  inference? := none, clauseLiterals? := none }

#eval show IO Unit from do
  -- A queued sibling is a valid dependency, not an active ancestor.
  let triangle := #[node "root" #["left", "right"], node "left" #["right"], node "right"]
  let ordered ← IO.ofExcept (parentsFirst triangle)
  unless ordered.map (·.name) == #["right", "left", "root"] do
    throw <| IO.userError "shared forward dependencies were replayed out of order"
  let diamond := #[node "root" #["left", "right"], node "right" #["leaf"],
    node "left" #["leaf", "leaf"], node "leaf", node "independent"]
  let ordered ← IO.ofExcept (parentsFirst diamond)
  unless ordered.map (·.name) == #["leaf", "left", "right", "root", "independent"] do
    throw <| IO.userError "parent order, duplicate citations, or independent roots changed"
  for (graph, diagnostic) in [
      (#[node "self" #["self"]], "cycle"),
      (#[node "a" #["b"], node "b" #["c"], node "c" #["a"]], "cycle"),
      (#[node "same", node "same"], "duplicate")] do
    match parentsFirst graph with
    | .ok _ => throw <| IO.userError s!"accepted a graph with {diagnostic} dependencies"
    | .error message => unless message.contains diagnostic do
        throw <| IO.userError s!"unexpected graph diagnostic: {message}"
  let missing := #[node "child" #["unknown"]]
  unless (← IO.ofExcept (parentsFirst missing)).map (·.name) == #["child"] do
    throw <| IO.userError "missing parents must remain for replay's boundary diagnostic"
  -- No recursion limit or quadratic ancestor scan on a deep proof.
  let chain := (List.range 10000).reverse.toArray.map fun index =>
    node s!"f{index}" (if index == 0 then #[] else #[s!"f{index - 1}"])
  let ordered ← IO.ofExcept (parentsFirst chain)
  unless ordered.size == 10000 && (ordered[0]?.map (·.name)) == some "f0" &&
      (ordered[9999]?.map (·.name)) == some "f9999" do
    throw <| IO.userError "lost or misordered a deep proof chain"

  -- Duplicate names must be rejected before SAT collapsing removes them.
  let path := "artifacts/decoder-graph-tests.tstp"
  IO.FS.writeFile path <| String.join [
    "tff(b,axiom,p,file('input',fact0)).\n",
    "tff(internal,plain,p,inference(sat_conversion,[],[b])).\n",
    "tff(internal,plain,p,inference(sat_conversion,[],[b])).\n",
    "tff(final,plain,$false,inference(avatar_sat_refutation,[],[internal])).\n"]
  let proof ← IO.ofExcept (← parseVampireTSTP
    "" path)
  let problem : TFF.Problem := {
    text := "", sorts := #[], facts := #[], symbols := #[("p", .atom 0, .base .prop)] }
  match Replay.decodeSteps problem proof with
  | .ok _ => throw <| IO.userError "SAT collapsing hid a duplicate step name"
  | .error message => unless message.contains "duplicate Vampire proof step `internal`" do
      throw <| IO.userError s!"unexpected duplicate-name diagnostic: {message}"
  IO.println "Proof graph: shared dependencies, malformed graphs, and 10000-node chain passed"
