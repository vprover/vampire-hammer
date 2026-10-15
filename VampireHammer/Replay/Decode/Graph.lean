import VampireHammer.Replay.Types

/-! Dependency ordering at the decoded proof boundary. -/

namespace VampireHammer.Replay.Decode.Internal

open VampireHammer.Backend

private inductive Visit where
  | enter (step : Step)
  | leave (step : Step)

/-- Move each step after its known parents, visiting roots in file order and
parents in certificate order. Only active ancestors indicate a cycle: queued
siblings may share dependencies. Each node and edge is visited once, without
recursive calls or repeated scans of the pending stack.

Missing parents remain for replay's unavailable-parent diagnostic. Duplicate
names and cycles fail here instead of silently dropping or misordering nodes. -/
def parentsFirst (steps : Array Step) : Except String (Array Step) := do
  let mut byName : Std.HashMap String Step := {}
  for step in steps do
    if byName.contains step.name then
      throw s!"duplicate Vampire proof step `{step.name}`"
    byName := byName.insert step.name step
  let mut emitted : Std.HashSet String := {}
  let mut active : Std.HashSet String := {}
  let mut ordered := #[]
  for step in steps do
    let mut stack := [Visit.enter step]
    while true do
      let visit :: rest := stack | break
      stack := rest
      match visit with
      | .leave current =>
        active := active.erase current.name
        emitted := emitted.insert current.name
        ordered := ordered.push current
      | .enter current =>
        if emitted.contains current.name then continue
        if active.contains current.name then
          throw s!"cycle in Vampire proof dependencies at step `{current.name}`"
        active := active.insert current.name
        stack := .leave current :: stack
        for parent in current.parents.reverse do
          if emitted.contains parent.name then continue
          if let some parent := byName.get? parent.name then
            stack := .enter parent :: stack
  pure ordered

end VampireHammer.Replay.Decode.Internal
