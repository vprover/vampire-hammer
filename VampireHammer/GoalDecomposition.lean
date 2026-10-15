import Auto.Tactic
import Lean.Meta.Tactic.Ext

/-! Bounded structural preparation using constructor/extensionality metadata
and only the caller's already-selected facts. No global simp index is consulted. -/

open Lean Meta

register_option vampire.decomposeGoals : Bool := {
  defValue := true
  descr := "Try bounded constructor and extensionality decomposition after the original export attempt"
}

register_option vampire.decompositionGoalLimit : Nat := {
  defValue := 8
  descr := "Maximum generated subgoals in structural goal preparation"
}

register_option vampire.monoDecomposition : Bool := {
  defValue := true
  descr := "Try bounded constructor decomposition before the HO retry when the default/sliced FO monomorphization window expires"
}

namespace VampireHammer.GoalDecomposition

def isCandidate (goal : MVarId) : MetaM Bool := goal.withContext do
  let target ← withTransparency .default <| whnf (← goal.getType)
  if let some (type, _, _) := target.eq? then
    unless ← isProp type do
      return !(← Ext.getExtTheorems type).isEmpty
  let .const name _ := target.getAppFn | return false
  let env ← getEnv
  let some (.inductInfo info) := env.find? name | return false
  return (Lean.getStructureInfo? env name).isSome && info.ctors.length == 1 && info.numIndices == 0

/-- Construct only records whose remaining fields are all propositions. Never
choose an existential witness or a data field. Restore state on rejection. -/
def split? (goal : MVarId) (limit : Nat) : MetaM (Option (Array MVarId)) := goal.withContext do
  let target ← withTransparency .default <| whnf (← goal.getType)
  let .const name _ := target.getAppFn | return none
  let env ← getEnv
  unless (Lean.getStructureInfo? env name).isSome do return none
  let some (.inductInfo info) := env.find? name | return none
  unless info.ctors.length == 1 && info.numIndices == 0 do return none
  let saved ← saveState
  try
    let goals ← goal.apply (← mkConstWithFreshMVarLevels info.ctors.head!)
    if goals.length > limit then
      saved.restore
      return none
    unless ← goals.allM (fun goal => goal.withContext do isProp (← goal.getType)) do
      saved.restore
      return none
    return some goals.toArray
  catch _ =>
    saved.restore
    return none

/-- Simplify the target with selected facts only. Original local declarations
are retained, so explicit hints still resolve and unselected hypotheses cannot
participate. A failed optional simplification restores its metavariable state. -/
def simplify (goal : MVarId) (facts : Array Auto.Lemma) : MetaM (Option MVarId) := goal.withContext do
  let saved ← saveState
  try
    Auto.Meta.withMaxHeartbeats 8000 do
      let mut theorems : SimpTheoremsArray := #[]
      for fact in facts[:min facts.size 64] do
        unless fact.params.isEmpty do continue
        let step ← saveState
        try
          theorems ← theorems.addTheorem (.other (← mkFreshId)) fact.proof
        catch _ => step.restore
      let context ← Simp.mkContext
        { maxSteps := 512, zetaDelta := false, contextual := true }
        theorems
      return (← simpTarget goal context).1
  catch _ =>
    saved.restore
    return some goal

/-- Apply at most one registered extensionality theorem. Exclude the theorem
being reproved and reject generated data/witness goals. Failed candidates do
not leave assignments behind. -/
def extensionality? (goal : MVarId) (limit : Nat) (exclude? : Option Name) :
    MetaM (Option (Array MVarId)) := goal.withContext do
  let some (type, _, _) := (← instantiateMVars (← goal.getType)).eq? | return none
  if ← isProp type then return none
  let candidates ← Ext.getExtTheorems type
  for candidate in candidates[:min candidates.size 8] do
    if exclude? == some candidate.declName then continue
    let saved ← saveState
    try
      let goals ← goal.apply (← mkConstWithFreshMVarLevels candidate.declName)
      if goals.length > limit then
        saved.restore
        continue
      unless ← goals.allM (fun goal => goal.withContext do isProp (← goal.getType)) do
        saved.restore
        continue
      return some goals.toArray
    catch _ => saved.restore
  return none

end VampireHammer.GoalDecomposition
