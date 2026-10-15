import VampireHammer.Replay.Diagnostics
import VampireHammer.Options

register_option vampire.diagnosticCase : String := {
  defValue := ""
  descr := "Case identity attached to durable diagnostic events in batched benchmarks"
}

namespace VampireHammer.Export
open Lean Meta

/-- Carry the actual missing type through rollback, using ordinary diagnostic
metadata. Recovery must never parse a pretty-printed Lean expression. -/
def missingDomainMessage (message : String) (type : Expr) : MetaM MessageData := do
  let display ← ppExpr type
  let payload := MessageData.tagged `vampire.missingDomain <|
    MessageData.withExprHover display type (← getLCtx)
  return m!"{message} (missing domain is `{payload}`)"

partial def missingDomainType? : MessageData → Option Expr
  | .tagged `vampire.missingDomain (.ofFormatWithInfos value) =>
    match value.infos.get? 0 with
    | some (.ofDelabTermInfo info) => some info.expr
    | _ => none
  | .withContext _ body | .withNamingContext _ body | .nest _ body | .group body |
      .tagged _ body | .ofOriginatingSyntax _ body => missingDomainType? body
  | .compose left right => missingDomainType? left <|> missingDomainType? right
  | _ => none

/-- Append machine-readable events outside speculative tactic state. The
output path belongs to this goal; the live stream is used by benchmark runs. -/
def diagnosticsEnabled : CoreM Bool := do
  let options ← getOptions
  return !(vampire.outputPath.get options).isEmpty

def diagnosticEvent (event : String) (fields : List (String × Json) := []) : MetaM Unit := do
  let options ← getOptions
  let destination := vampire.outputPath.get options
  if destination.isEmpty then return
  let entry := Json.mkObj (("event", toJson event) ::
    ("name", toJson (vampire.diagnosticCase.get options)) :: fields)
  let line := entry.compress
  let path : System.FilePath := destination ++ ".events.jsonl"
  if let some parent := path.parent then IO.FS.createDirAll parent
  IO.FS.withFile path .append fun stream => stream.putStrLn line
  -- Named benchmark cases also expose failure events in their captured logs.
  unless (vampire.diagnosticCase.get options).isEmpty do
    let stderr ← IO.getStderr
    stderr.putStrLn ("[vampire.event] " ++ line)
    stderr.flush

end VampireHammer.Export
