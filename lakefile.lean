import Lake
open Lake DSL System

/-!
Core dependencies and the bundled Vampire build. See `vendor/README.md`.
Use `lake -R -Kkey=value build` after changing configuration.
Optional tests and benchmarks use `mathlib=true`.
-/

package vampire_hammer where
  version := v!"0.1.0"
  extraDepTargets := #[`vampire]

require auto from git "https://github.com/i-am-a-teapot/lean-auto" @
  "a2f825aca7e56ac2f6b3b502bc1290369fc6d5f5"

require vamplean from git "https://github.com/vprover/vamplean" @
  "fda0586b716ae9844bb33cbe0d2053730afcc16b"

require tptp_parser from "vendor/tptp_parser"

meta if get_config? mathlib == some "true" then
  require mathlib from git "https://github.com/leanprover-community/mathlib4" @ "v4.34.1"

@[default_target]
lean_lib VampireHammer where
  -- Load native tactic code in the editor and with `lake lean FILE`.
  precompileModules := true

-- Keep benchmark harnesses interpreted so they can call lean-auto's
-- non-native evaluation helpers while loading the compiled tactic library.
meta if get_config? mathlib == some "true" then
  @[default_target]
  lean_lib VampireHammerBenchmarkMathlib where
    roots := #[`VampireHammer.Benchmark.Mathlib]

lean_exe «vampire-preprocess» where
  root := `VampireHammer.CLI

/-- Pinned Vampire commit with the replay and higher-order certificates
this package consumes, from the `tptp-replay-annotations` branch. -/
def vampireRevision : String := "6ee1f120df1b6c38705066dcbe7c858c09b12ded"

def vampireRepository : String :=
  (get_config? vampireRepository).getD "https://github.com/vprover/vampire"

def buildVampire : Bool := (get_config? buildVampire) != some "false"

def vampireStatic : Bool := (get_config? vampireStatic) == some "true"

/-- Parallel compile jobs: one per core, but at most one per 2 GB of available
memory, since Vampire's translation units are memory-hungry. -/
def vampireJobs : LogIO Nat := do
  if let some jobs := (get_config? vampireJobs).bind String.toNat? then
    return max jobs 1
  let query (cmd : String) (args : Array String) : LogIO (Option Nat) := do
    try
      return (← captureProc { cmd, args }).trimAscii.toString.toNat?
    catch _ => return none
  let cores := (← query "getconf" #["_NPROCESSORS_ONLN"]).getD 1
  let memoryGiB ← do
    if ← FilePath.pathExists "/proc/meminfo" then
      let available := (← IO.FS.lines "/proc/meminfo").findSome? fun line =>
        if line.startsWith "MemAvailable:" then
          ((line.drop "MemAvailable:".length).trimAscii.toString.takeWhile Char.isDigit).toNat?
        else none
      pure <| available.map (· / (1024 * 1024))
    else
      -- macOS reports total memory only; assume half of it is available.
      pure <| (← query "sysctl" #["-n", "hw.memsize"]).map (· / (2 * 1024 * 1024 * 1024))
  let byMemory := memoryGiB.map (· / 2) |>.getD cores
  return max 1 (min cores byMemory)

private def gitOutput (repository : FilePath) (args : Array String) : LogIO String := do
  let output ← captureProc { cmd := "git", args := #["-C", repository.toString] ++ args }
  return output.trimAscii.toString

/-- Fetch the pinned Vampire commit (shallow; CMake fetches the `cadical`
and `viras` submodules it needs) and build a Release binary. The build is
redone when the pinned commit or linking mode changes. -/
target vampire pkg : FilePath := Job.async do
  let root := pkg.lakeDir / "vampire"
  let source := root / "source"
  let build := root / "build"
  let executable := build / "vampire"
  unless buildVampire do return executable
  let stamp := root / "built-from"
  unless ← (source / ".git").pathExists do
    IO.FS.createDirAll source
    proc { cmd := "git", args := #["init", source.toString] }
  let checkedOut ← try gitOutput source #["rev-parse", "--verify", "HEAD"]
    catch _ => pure ""
  unless checkedOut == vampireRevision do
    logInfo s!"fetching Vampire commit `{vampireRevision}` from {vampireRepository}"
    proc { cmd := "git", args := #["-C", source.toString, "fetch", "--depth", "1",
      vampireRepository, vampireRevision] }
    proc { cmd := "git", args := #["-C", source.toString, "checkout", "--detach", vampireRevision] }
  let commit ← gitOutput source #["rev-parse", "HEAD"]
  unless commit == vampireRevision do
    error s!"Vampire checkout is at {commit}, expected {vampireRevision}"
  let linking := if vampireStatic then "static" else "dynamic"
  let wanted := s!"{commit} {linking}"
  if (← executable.pathExists) && (← stamp.pathExists) then
    if (← IO.FS.readFile stamp).trimAscii.toString == wanted then
      return executable
  let jobs ← vampireJobs
  logInfo s!"building Vampire {wanted} with {jobs} parallel jobs"
  proc { cmd := "cmake", args := #["-S", source.toString, "-B", build.toString,
    "-DCMAKE_BUILD_TYPE=Release",
    if vampireStatic then "-DBUILD_SHARED_LIBS=OFF" else "-DBUILD_SHARED_LIBS=ON",
    "-DTHREADS_PREFER_PTHREAD_FLAG=ON"] }
  proc { cmd := "cmake", args := #["--build", build.toString, "--target", "vampire",
    "--parallel", toString jobs] }
  IO.FS.writeFile stamp (wanted ++ "\n")
  return executable
