import Auto.Tactic

namespace VampireHammer.Export

open Lean Meta

/-- One allocation deadline shared by every attempt of an optional search.
The allowance is capped at half of the caller's remaining heartbeats, leaving
room for the main proof route. A zero allowance disables the optional search. -/
structure SearchBudget where
  deadline : Nat

def SearchBudget.create (heartbeats : Nat) : MetaM SearchBudget := do
  let start ← IO.getNumHeartbeats
  let context ← readThe Core.Context
  let allowance := if context.maxHeartbeats == 0 then heartbeats * 1000 else
    min (heartbeats * 1000) ((context.initHeartbeats + context.maxHeartbeats - start) / 2)
  return ⟨start + allowance⟩

def SearchBudget.exhausted (budget : SearchBudget) : BaseIO Bool := do
  return (← IO.getNumHeartbeats) >= budget.deadline

/-- Run a transactional optional attempt without restarting its shared clock.
Failed candidates and local heartbeat timeouts restore metavariables and
messages. Cancellation, other runtime errors and caller exhaustion propagate. -/
def SearchBudget.run (budget : SearchBudget) (action : MetaM α) : MetaM (Option α) := do
  Core.checkInterrupted
  Core.checkMaxHeartbeats "optional search"
  if ← budget.exhausted then return none
  let start ← IO.getNumHeartbeats
  let remaining := budget.deadline - start
  if remaining == 0 then return none
  let saved ← saveState
  tryCatchRuntimeEx
    (do
      let result ← withTheReader Core.Context (fun context =>
        { context with initHeartbeats := start, maxHeartbeats := remaining }) <|
        withOptions (fun options =>
          let synthesis := synthInstance.maxHeartbeats.get options
          let cap := max 1 (remaining / 1000)
          options.set `synthInstance.maxHeartbeats
            (if synthesis == 0 then cap else min synthesis cap)) do
          let result ← action
          Core.checkSystem "optional search"
          return result
      -- Restore the caller's deadline before checking it.
      Core.checkMaxHeartbeats "optional search"
      return some result)
    fun error => do
      saved.restore
      Core.checkInterrupted
      Core.checkMaxHeartbeats "optional search"
      if error.isInterrupt || (error.isRuntime && !error.isMaxHeartbeat) then throw error
      return none

end VampireHammer.Export

namespace VampireHammer.Export
open Lean Meta

/-- A cumulative allowance for optional passes separated by required work.
Each invocation uses an absolute SearchBudget, but only allocations inside
those invocations consume this allowance. Required preprocessing or replay
between them cannot expire an allowance which has not been used yet. -/
structure SearchAllowance where
  remaining : IO.Ref Nat

def SearchAllowance.create (heartbeats : Nat) : IO SearchAllowance := do
  return ⟨← IO.mkRef heartbeats⟩

def SearchAllowance.run (allowance : SearchAllowance) (action : MetaM α) : MetaM (Option α) := do
  let budget ← SearchBudget.create (← allowance.remaining.get)
  let start ← IO.getNumHeartbeats
  try
    budget.run action
  finally
    let consumed := ((← IO.getNumHeartbeats) - start + 999) / 1000
    allowance.remaining.modify (· - consumed)

end VampireHammer.Export
