import Lean

namespace VampireHammer.UserMessages

open Lean Elab Tactic

/-- Advice for the final failure, after all search and recovery attempts.
Keep the underlying error intact so its statement and diagnostic tags survive. -/
def failureHint (message : String) : String :=
  if message.contains "Could not start Vampire executable" then
    "Build the bundled prover with `lake build vampire`, or set `(executable := \"/path/to/vampire\")`."
  else if message.contains "timed out" || message.contains "proof-search budget exhausted" then
    "Try a longer search, for example `vampire (timeout := 20) [h₁, h₂]`, or supply more relevant premises."
  else if message.contains "no known inhabitation evidence" then
    "Provide a value or a `Nonempty` instance for the reported type if it is inhabited. An empty type cannot be assumed inhabited."
  else if message.contains "SZS status Satisfiable" || message.contains "SZS status CounterSatisfiable" then
    "The exported premises do not imply the exported goal. Add relevant premises or unfold a definition with `(unfold := [name])`; this does not show that the Lean goal is false."
  else if message.contains "Could not decode" || message.contains "Could not parse Vampire" ||
      message.contains "replay" || message.contains "reconstruct" || message.contains "Vampire step" then
    "Retain the problem and certificate with `(outputPath := \"artifacts/failure.p\")`. Enable `set_option trace.vampire true` for details."
  else if message.contains "export:" || message.contains "Monomorphization" then
    "Try a smaller explicit premise list or unfold the reported definition with `(unfold := [name])`."
  else
    "Try explicit premises with `vampire [h₁, h₂]` or all local hypotheses with `vampire [*]`. Enable `set_option trace.vampire true` for details."

def withFailureHint (action : TacticM Unit) : TacticM Unit := do
  try action catch error =>
    if error.isInterrupt || error.isRuntime then throw error
    let hint := failureHint (← error.toMessageData.toString)
    throwError "vampire could not close the goal.\n{error.toMessageData}\n\n{hint}"

end VampireHammer.UserMessages
