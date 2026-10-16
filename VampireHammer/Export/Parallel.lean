import VampireHammer.Options

namespace VampireHammer.Export.Internal

open Lean Meta

/-- On a single allocated processor, retain both alternatives without running
two provers at once. A failed attempt restores the complete Lean state. -/
def firstSuccessfulMeta (actions : Array (MetaM α)) : MetaM α := do
  let saved ← saveState
  let mut errors := #[]
  for action in actions do
    try return ← action
    catch error =>
      if error.isInterrupt || error.isRuntime then throw error
      errors := errors.push error.toMessageData
      saved.restore
  throwError m!"All sequential Vampire attempts failed:\n{MessageData.joinSep errors.toList m!"\n"}"

/-- Race isolated metavariable states. Only a successful worker's complete state
is committed. Fresh names are split by `wrapAsync`; cancellation reaches external
processes through the worker's token. All workers are joined before returning. -/
def raceMeta (actions : Array (MetaM α)) : MetaM α := do
  if actions.isEmpty then throwError "No parallel Vampire attempts were available"
  let context ← read
  let state ← get
  let parent := (← readThe Core.Context).cancelTk?
  -- Keep the registry in a ref: a return/exception in the try body must not
  -- roll local mutations back before the finally block cancels the workers.
  let workers ← IO.mkRef #[]
  try
    for action in actions do
      let token ← IO.CancelToken.new
      if let some parent := parent then parent.onSet token.set
      let wrapped ← Core.wrapAsync (fun () => do
        let (value, metaState) ← action.run context state
        return (value, ← get, metaState)) (some token)
      let task ← (wrapped ()).asTask .dedicated
      workers.modify (·.push (token, task))
    let mut pending := (← workers.get).map (·.2)
    let mut errors : Array MessageData := #[]
    while !pending.isEmpty do
      Core.checkInterrupted
      let mut next := #[]
      for task in pending do
        if ← IO.hasFinished task then
          match task.get with
          | .ok (value, coreState, metaState) =>
            set coreState
            set metaState
            return value
          | .error error =>
            if error.isInterrupt || error.isRuntime then throw error
            errors := errors.push error.toMessageData
        else next := next.push task
      pending := next
      unless pending.isEmpty do IO.sleep 10
    throwError m!"All parallel Vampire attempts failed:\n{MessageData.joinSep errors.toList m!"\n"}"
  finally
    for (token, _) in ← workers.get do token.set
    for (_, task) in ← workers.get do discard <| IO.wait task

end VampireHammer.Export.Internal
