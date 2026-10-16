#!/usr/bin/env python3
"""Run VampireHammer Lean and Python regressions."""

import argparse
import json
import os
from pathlib import Path
import shutil
import signal
import subprocess
import time
import unittest


PROJECT = Path(__file__).resolve().parents[1]
LEAN_TEST_DIRECTORIES = ("Tests",)
PYTHON_TEST_DIRECTORIES = ("Tests/Python",)
# These exercises invoke the real prover; the other regression files use
# checked fixtures or test the metaprogramming/proof interfaces directly.
REAL_PROVER_FILES = {
    "FactReportingTests.lean",
    "OnlyFactsTests.lean",
    "CentralSquaresExample.lean",
    "FoolConditionalTests.lean",
    "BoolBridgeTests.lean",
    "StructureLawTests.lean",
    "StructureLawFallbackTests.lean",
    "HeterogeneousEqualityTests.lean",
    "DirectSubstitutionTests.lean",
    "ConstructorFactsTests.lean",
    "AttributeLemmaTests.lean",
    "GoalBinderTests.lean",
    "SortReplayTests.lean",
    "ProofArgumentNormalizationTests.lean",
    "GoalDecompositionTests.lean",
    "MonoDecompositionTests.lean",
    "AutomaticUnfoldingTests.lean",
    "DomainInhabitationTests.lean",
    "HigherOrderInhabitationTests.lean",
    "HigherOrderOptionalPremiseTests.lean",
    "HigherOrderFallbackTests.lean",
    "HigherOrderSearchRetryTests.lean",
    "HigherOrderScalarTests.lean",
    "StagedSearchTests.lean",
    "RoutedSearchTests.lean",
    "ParallelSearchTests.lean",
    "ProofCacheTests.lean",
    "UserMessagesTests.lean",
    "ProofAttributionTests.lean",
    "TranslationRecoveryTests.lean",
    "EmptyDomainRecoveryTests.lean",
    "FunctionEqualityTests.lean",
    "FirstOrderEncodingTests.lean",
    "ConditionalEncodingTests.lean",
    "HigherOrderConditionalTests.lean",
    "StructureProjectionTests.lean",
    "OpaqueQuantifierTests.lean",
    "FiniteSetTests.lean",
    "InstanceDefinitionTests.lean",
    "LawInstancesTests.lean",
    "SiblingLemmasTests.lean",
    "EqualityFactoringExample.lean",
    "FactoringExample.lean",
    "MathlibHammerTests.lean",
    "MathlibFailureRegressionTests.lean",
    "TranslationAlignmentTests.lean",
    "OptionalPremiseTests.lean",
    "PortfolioReplayTests.lean",
    "PropositionClassTests.lean",
    "RealEqualityFactoringExample.lean",
    "RealSuperpositionExample.lean",
    "ResolutionExample.lean",
    "SkolemReplayTest.lean",
    "SkolemizationExample.lean",
    "SourceSyntaxTests.lean",
    "SuperpositionTest.lean",
    "TptpRegressionTests.lean",
}


def python_tests():
    """Discover the Python regressions included in this checkout."""
    suite = unittest.TestSuite()
    for directory in PYTHON_TEST_DIRECTORIES:
        start = str(PROJECT / directory)
        suite.addTests(unittest.TestLoader().discover(start, top_level_dir=start))
    return suite


def test_ids(suite):
    for test in suite:
        if isinstance(test, unittest.TestSuite):
            yield from test_ids(test)
        else:
            yield test.id()


def regression_files(suite):
    # Only top-level demonstrations belong to the regular suites;
    # Examples/Exploratory remains available through explicit selection.
    files = sorted(
        [*(path for directory in LEAN_TEST_DIRECTORIES
           for path in PROJECT.joinpath(directory).rglob("*.lean")),
         *PROJECT.joinpath("Examples").glob("*.lean")]
    )
    return [
        path for path in files
        if suite == "all" or (path.name in REAL_PROVER_FILES) == (suite == "real")
    ]


def resolve_file(name):
    """Accept project-relative paths and unique basenames for focused runs."""
    path = (PROJECT / name).resolve()
    if path.is_relative_to(PROJECT) and path.suffix == ".lean" and path.is_file():
        return path
    if Path(name).name == name:
        matches = [path for directory in (*LEAN_TEST_DIRECTORIES, "Examples")
                   for path in (PROJECT / directory).rglob(name)]
        if len(matches) == 1:
            return matches[0]
    raise ValueError(f"expected a project Lean file or unique test basename: {name}")


def run_test(path, output, timeout, vampire):
    # The caller validates the prebuilt prover for real tests; certificates
    # use fixtures. Neither route needs Lake to clone or rebuild Vampire.
    command = ["lake", "-R", "-KbuildVampire=false"]
    imports = [line for line in path.read_text().splitlines() if line.startswith("import ")]
    if any("Mathlib" in line for line in imports):
        command.append("-Kmathlib=true")
    relative = path.relative_to(PROJECT)
    # `lake lean` loads the precompiled hammer and lean-auto libraries, as the
    # editor does; `lake env lean` would interpret their code, much slower.
    command.extend(["lean", str(relative), "--", "-j", "1"])
    if vampire:
        # Direct-interface tests import only narrow modules that do not
        # register tactic options. Lean's weak setting is ignored there.
        command.append(f"-Dweak.vampire.executable={vampire}")
    started = time.monotonic()
    log_path = output / relative.with_suffix(".log")
    log_path.parent.mkdir(parents=True, exist_ok=True)
    timed_out = False
    environment = os.environ.copy()
    if vampire:
        environment["VAMPIRE_BIN"] = str(Path(vampire).resolve())
    with log_path.open("w") as log:
        # A timeout must also stop any Vampire processes started by Lean.
        process = subprocess.Popen(
            command, cwd=PROJECT, stdout=log, stderr=subprocess.STDOUT,
            start_new_session=True, env=environment,
        )
        try:
            returncode = process.wait(timeout=timeout)
        except (subprocess.TimeoutExpired, KeyboardInterrupt) as error:
            os.killpg(process.pid, signal.SIGKILL)
            process.wait()
            if isinstance(error, KeyboardInterrupt):
                raise
            returncode = process.returncode
            timed_out = True
    return {
        "file": relative.as_posix(),
        "passed": returncode == 0 and not timed_out,
        "returncode": returncode,
        "timed_out": timed_out,
        "seconds": round(time.monotonic() - started, 3),
        "log": str(log_path),
    }


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("files", nargs="*", help="project-relative Lean paths or unique test basenames")
    parser.add_argument("--suite", choices=("certificates", "real", "python", "all"), default="certificates",
                        help="all includes Python tests and all Lean regressions")
    parser.add_argument("--list", action="store_true", help="list selected tests without running")
    parser.add_argument("--timeout", type=float, default=150, help="wall limit per file in seconds")
    parser.add_argument(
        "--vampire", default=str(PROJECT / ".lake/vampire/build/vampire"),
        help="real Vampire executable; source-level fixture settings still apply",
    )
    parser.add_argument("--output", type=Path, default=Path("artifacts/regression-tests"))
    args = parser.parse_args()
    if args.timeout <= 0:
        parser.error("timeout must be positive")
    if args.suite == "python":
        if args.files:
            parser.error("--suite python does not accept Lean file selections")
        suite = python_tests()
        if args.list:
            print("\n".join(test_ids(suite)))
            return 0
        return 0 if unittest.TextTestRunner().run(suite).wasSuccessful() else 1
    try:
        files = [resolve_file(name) for name in args.files] if args.files else regression_files(args.suite)
    except ValueError as error:
        parser.error(str(error))
    if args.list:
        for path in files:
            print(path.relative_to(PROJECT).as_posix())
        if args.suite == "all" and not args.files:
            print("\n".join(test_ids(python_tests())))
        return 0
    binary = shutil.which(args.vampire)
    if binary is None and any(path.name in REAL_PROVER_FILES for path in files):
        parser.error(f"Vampire executable not found: {args.vampire}")
    args.vampire = str(Path(binary).resolve()) if binary else None
    python_passed = True
    if args.suite == "all" and not args.files:
        python_passed = unittest.TextTestRunner().run(python_tests()).wasSuccessful()
    output = args.output if args.output.is_absolute() else PROJECT / args.output
    output.mkdir(parents=True, exist_ok=True)
    rows = []
    for path in files:
        row = run_test(path, output, args.timeout, args.vampire)
        rows.append(row)
        (output / "results.json").write_text(json.dumps(rows, indent=2) + "\n")
        status = "PASS" if row["passed"] else "TIMEOUT" if row["timed_out"] else "FAIL"
        print(f"{status} {row['file']} ({row['seconds']:.2f}s)", flush=True)
    passed = sum(row["passed"] for row in rows)
    print(f"{passed}/{len(rows)} passed; logs: {output}")
    return 0 if passed == len(rows) and python_passed else 1


if __name__ == "__main__":
    raise SystemExit(main())
