import VampireHammer.TSTP
import Std.Sync.Barrier

open VampireHammer

private def parserLibrary := ""

private def awaitWorkers (tasks : Array (Task (Except IO.Error Unit))) : IO Unit := do
  for task in tasks do
    IO.ofExcept task.get

/-! Exercise simultaneous first use, independent scanner buffers and results,
and syntax/lexical errors interleaved with successful parses. Half the warm
workers call the parser directly, bypassing the hammer's loading adapter. -/
#eval show IO Unit from do
  let directory : System.FilePath := "artifacts/parser-concurrency"
  IO.FS.createDirAll directory
  let workers := 8
  let barrier ← Std.Barrier.new workers
  let mut coldPaths := #[]
  for worker in [:workers] do
    let path := directory / s!"cold-{worker}.p"
    let text := String.join <| (List.range (worker + 1)).map fun index =>
      s!"cnf(worker{worker}_{index},axiom,p{worker}).\n"
    IO.FS.writeFile path text
    coldPaths := coldPaths.push path
  -- A failed library lookup must not poison later initialization.
  let rejected ← try
    let _ ← parseVampireTSTP (directory / "missing-library.so").toString coldPaths[0]!.toString
    pure false
  catch _ => pure true
  unless rejected do throw <| IO.userError "accepted a missing parser library"

  let mut tasks := #[]
  for worker in [:workers] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) do
      let _ ← barrier.wait
      let parsed ← IO.ofExcept (← parseVampireTSTP parserLibrary coldPaths[worker]!.toString)
      let .mk inputs := parsed
      unless inputs.length == worker + 1 && (reprStr parsed).contains s!"worker{worker}_" do
        throw <| IO.userError s!"first-use parse mixed worker {worker}'s input or result")
  awaitWorkers tasks

  let longInput := String.join <| (List.range 160).map fun index =>
    s!"tff(long{index},axiom,(! [X : person,Y : person] : (relation(X,Y) => relation(Y,X)))).\n"
  let cases := #[
    "% comments only\n/* empty proof */\n",
    "cnf('quoted name',axiom,(p | ~q),inference(resolution,[status(thm)],[left,right])).\n",
    "tff(sort,type,person:$tType).\ntff(r,type,relation:(person * person)>$o).\n" ++ longInput,
    "fof(f,axiom,(! [X] : (? [Y] : (p(X,Y) <=> q(Y))))).\n",
    "fof(f,plain,($ite((p & q),a,$ite(q,b,a)) = a)).\nfof(g,plain,p).\n",
    "thf(f,plain,((= @ a) @ a)).\ntff(g,plain,~ a = b).\n",
    "tff(number,axiom,(f(-123,4/7,1.25E-3) = g(\"distinct\"))).\n"
  ]
  let mut paths := #[]
  let mut expected := #[]
  for index in [:cases.size] do
    let path := directory / s!"valid-{index}.p"
    IO.FS.writeFile path cases[index]!
    paths := paths.push path
    expected := expected.push (reprStr (← IO.ofExcept (← parseVampireTSTP parserLibrary path.toString)))
  let syntaxError := directory / "syntax-error.p"
  let lexicalError := directory / "lexical-error.p"
  IO.FS.writeFile syntaxError "fof(bad,axiom,($ite(p,a,b) = )).\n"
  -- The parser can finish a complete AST before the scanner reports this error.
  IO.FS.writeFile lexicalError "cnf(good,axiom,p).\n§\n"
  let invalidPaths := #[syntaxError, lexicalError, directory / "missing-input.p"]

  tasks := #[]
  for worker in [:workers] do
    tasks := tasks.push (← IO.asTask (prio := .dedicated) do
      let parse := fun (path : System.FilePath) =>
        if worker % 2 == 0 then parseVampireTSTP parserLibrary path.toString
        else Tptp.Parser.parseFile path.toString
      let _ ← barrier.wait
      for iteration in [:64] do
        let invalid := invalidPaths[(worker + iteration) % invalidPaths.size]!
        match ← parse invalid with
        | .error _ => pure ()
        | .ok _ => throw <| IO.userError s!"worker {worker} accepted invalid input {invalid}"
        let index := (worker + iteration) % paths.size
        let parsed ← IO.ofExcept (← parse paths[index]!)
        unless reprStr parsed == expected[index]! do
          throw <| IO.userError s!"worker {worker} mixed scanner state or retained a previous parse result")
  awaitWorkers tasks
  IO.println "Parser concurrency: 8 simultaneous first-use calls and 1024 mixed valid/invalid parses passed"
