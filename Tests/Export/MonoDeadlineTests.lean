import VampireHammer
import VampireHammer.Export.Pipeline

open Lean Meta Elab Tactic VampireHammer.Export.Internal

elab "check_mono_deadline" : tactic => withMainContext do
  let run (action : (MetaM Bool → MetaM Bool) → MetaM Bool) :=
    withOptions (·.set `vampire.monoHeartbeats (10 : Nat)) <| withMonoDeadline action
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let expired ← tryCatchRuntimeEx
    (run fun resume => do
      pending.mvarId!.assign (mkNatLit 7)
      IO.addHeartbeats 20000
      resume (pure true))
    (fun error => do
      unless (← error.toMessageData.toString).contains
          "first-order monomorphization heartbeat window exhausted" do throw error
      pure false)
  if expired || (← pending.mvarId!.isAssigned) then
    throwError "monomorphization exhaustion failed to restore state"
  -- Export/replay may exceed the mono window under the caller's deadline.
  let completed ← run fun resume => resume do
    IO.addHeartbeats 20000
    Core.checkSystem "test export"
    pure true
  unless completed do throwError "mono window included export/replay"
  -- Unsupported export can trigger another monomorphization attempt.
  let expired ← tryCatchRuntimeEx
    (run fun resume => do
      try
        resume (throwError "unsupported export")
      catch _ =>
        IO.addHeartbeats 20000
        resume (pure true))
    (fun error => do
      unless (← error.toMessageData.toString).contains
          "first-order monomorphization heartbeat window exhausted" do throw error
      pure false)
  if expired then throwError "translation retries disabled the mono window"
  let propagated ← tryCatchRuntimeEx
    (run fun resume => resume do
      withTheReader Core.Context (fun current =>
        { current with initHeartbeats := 0, maxHeartbeats := 1 }) do
        Core.checkMaxHeartbeats "test replay"
        pure true)
    (fun error => do
      unless error.isMaxHeartbeat do throw error
      pure true)
  unless propagated do throwError "replay timeout became a mono timeout"
  let interrupted ← tryCatchRuntimeEx
    (run fun _ => throwInterruptException)
    (fun error => if error.isInterrupt then pure true else throw error)
  unless interrupted do throwError "mono window swallowed cancellation"

  for options in [fun (options : Options) => options.set `vampire.monoHeartbeats (0 : Nat),
      fun (options : Options) => options.set `vampire.higherOrder true] do
    let completed ← withOptions (fun current => options (current.set `vampire.monoHeartbeats (10 : Nat))) <|
      withMonoDeadline fun resume => do
      IO.addHeartbeats 20000
      Core.checkSystem "unwindowed mono"
      resume (pure true)
    unless completed do throwError "disabled or native HO monomorphization was windowed"

  let start ← IO.getNumHeartbeats
  let propagated ← tryCatchRuntimeEx
    (withTheReader Core.Context (fun current =>
      { current with initHeartbeats := start, maxHeartbeats := 10000 }) <|
      run fun resume => do
        IO.addHeartbeats 20000
        resume (pure true))
    (fun error => if error.isMaxHeartbeat then pure true else throw error)
  unless propagated do throwError "mono window extended the caller's deadline"

  -- Branches receive the remainder of one additional mono allowance. Work
  -- in export/search/replay must not be subtracted from that allowance.
  let shared ← IO.mkRef 10000
  let first ← withOptions (·.set `vampire.monoHeartbeats (10 : Nat)) <|
    withMonoDeadline (fun resume => do
      IO.addHeartbeats 3000
      resume do
        IO.addHeartbeats 20000
        Core.checkSystem "shared-budget replay"
        pure true) (some shared)
  let remaining ← shared.get
  unless first && remaining > 0 && remaining < 7000 do
    throwError "shared mono allowance included replay or did not charge mono: {remaining}"
  let pending ← mkFreshExprMVar (mkConst ``Nat)
  let expired ← tryCatchRuntimeEx
    (withOptions (·.set `vampire.monoHeartbeats (10 : Nat)) <|
      withMonoDeadline (fun resume => do
        pending.mvarId!.assign (mkNatLit 9)
        IO.addHeartbeats 8000
        resume (pure true)) (some shared))
    (fun error => do
      if isMonoDeadline (← error.toMessageData.toString) then pure true else throw error)
  unless expired && (← shared.get) == 0 && !(← pending.mvarId!.isAssigned) do
    throwError "next branch received a fresh mono allowance or failed to roll back"
  let entered ← IO.mkRef false
  let expired ← tryCatchRuntimeEx
    (withOptions (·.set `vampire.monoHeartbeats (10 : Nat)) <|
      withMonoDeadline (fun _ => do
        entered.set true
        pure false) (some shared))
    (fun error => do
      if isMonoDeadline (← error.toMessageData.toString) then pure true else throw error)
  unless expired && !(← entered.get) do
    throwError "exhausted shared allowance started another branch"

set_option maxHeartbeats 1000 in
example : True := by
  check_mono_deadline
  trivial
