"""Regression discovery and invocation after reorganizing tests."""

import contextlib
import importlib.util
import io
from pathlib import Path
import sys
import tempfile
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[2] / "Tests/run-tests.py"
spec = importlib.util.spec_from_file_location("run_tests", SCRIPT)
runner = importlib.util.module_from_spec(spec)
spec.loader.exec_module(runner)


class RunnerTests(unittest.TestCase):
    def test_suites_partition_all_regressions(self):
        all_files = set(runner.regression_files("all"))
        certificates = set(runner.regression_files("certificates"))
        real = set(runner.regression_files("real"))
        self.assertEqual(all_files, certificates | real)
        self.assertFalse(certificates & real)
        self.assertEqual({p.name for p in real}, runner.REAL_PROVER_FILES)
        self.assertIn(runner.PROJECT / "Tests/Export/TffExporterTests.lean", certificates)
        self.assertIn(runner.PROJECT / "Examples/CentralSquaresExample.lean", real)
        self.assertFalse(any("Exploratory" in p.parts for p in all_files))
        self.assertEqual(all_files, set((runner.PROJECT / "Tests").rglob("*.lean")) |
                         set((runner.PROJECT / "Examples").glob("*.lean")))

    def test_paths_and_unique_basenames_select_same_file(self):
        expected = runner.PROJECT / "Tests/Parser/ParserNumberTests.lean"
        self.assertEqual(runner.resolve_file("ParserNumberTests.lean"), expected)
        self.assertEqual(runner.resolve_file("Tests/Parser/ParserNumberTests.lean"), expected)
        self.assertEqual(runner.resolve_file("CentralSquaresExample.lean"),
                         runner.PROJECT / "Examples/CentralSquaresExample.lean")

    def test_explicit_selection_can_include_exploratory_examples(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            example = project / "Examples/Exploratory/FailingExample.lean"
            example.parent.mkdir(parents=True)
            example.touch()
            with patch.object(runner, "PROJECT", project):
                self.assertEqual(runner.resolve_file("FailingExample.lean"), example)
                self.assertNotIn(example, runner.regression_files("all"))

    def test_python_discovery_covers_included_regressions(self):
        modules = {test_id.split('.')[0] for test_id in runner.test_ids(runner.python_tests())}
        self.assertEqual(modules, {"test_run_tests", "test_benchmark_mathlib"})

    def test_invalid_paths_and_ambiguous_basenames_are_rejected(self):
        with tempfile.TemporaryDirectory() as temporary:
            project = Path(temporary)
            for group in ("A", "B"):
                path = project / "Tests" / group / "SameTests.lean"
                path.parent.mkdir(parents=True)
                path.touch()
            with patch.object(runner, "PROJECT", project):
                for name in ("SameTests.lean", "Missing.lean", "../outside.lean"):
                    with self.subTest(name=name), self.assertRaises(ValueError):
                        runner.resolve_file(name)

    def test_invocation_keeps_project_cwd_and_separate_logs(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            path = runner.PROJECT / "Tests/Parser/ParserNumberTests.lean"
            with patch.object(runner.subprocess, "Popen") as popen:
                popen.return_value.wait.return_value = 0
                result = runner.run_test(path, output, 10, None)
            args, kwargs = popen.call_args
            command = args[0]
            # `lake lean` (native libraries), not `lake env lean` (interpreter).
            self.assertNotIn("env", command)
            self.assertIn("-KbuildVampire=false", command)
            self.assertEqual(command[command.index("lean") + 1], "Tests/Parser/ParserNumberTests.lean")
            self.assertEqual(command[command.index("lean") + 2], "--")
            self.assertEqual(kwargs["cwd"], runner.PROJECT)
            self.assertEqual(result["file"], "Tests/Parser/ParserNumberTests.lean")
            self.assertEqual(Path(result["log"]), output / "Tests/Parser/ParserNumberTests.log")
            self.assertTrue(result["passed"])

    def test_certificate_suite_does_not_require_a_prover(self):
        with tempfile.TemporaryDirectory() as temporary:
            argv = [str(SCRIPT), "ParserNumberTests.lean", "--vampire", "/missing/vampire",
                    "--output", temporary]
            with patch.object(sys, "argv", argv), patch.object(runner.shutil, "which", return_value=None), \
                 patch.object(runner, "run_test") as run, contextlib.redirect_stdout(io.StringIO()):
                run.return_value = {"file": "Tests/Parser/ParserNumberTests.lean",
                                    "passed": True, "seconds": 0}
                self.assertEqual(runner.main(), 0)
                self.assertIsNone(run.call_args.args[-1])

    def test_benchmark_invocation_enables_optional_dependencies(self):
        paths = [runner.PROJECT / "Tests/Frontend/MathlibBenchmarkTests.lean",
                 runner.PROJECT / "Tests/Frontend/SourceNormalizationTests.lean"]
        with tempfile.TemporaryDirectory() as temporary:
            for path in paths:
                with self.subTest(path=path), patch.object(runner.subprocess, "Popen") as popen:
                    popen.return_value.wait.return_value = 0
                    runner.run_test(path, Path(temporary), 10, None)
                    command = popen.call_args.args[0]
                    self.assertIn("-Kmathlib=true", command)

    def test_python_suite_runs_without_lean_or_vampire(self):
        argv = [str(SCRIPT), "--suite", "python", "--vampire", "/missing/vampire"]
        with patch.object(sys, "argv", argv), patch.object(runner, "python_tests") as discover, \
             patch.object(runner.unittest, "TextTestRunner") as text_runner, \
             patch.object(runner, "run_test") as run, patch.object(runner.shutil, "which") as which:
            text_runner.return_value.run.return_value.wasSuccessful.return_value = True
            self.assertEqual(runner.main(), 0)
            text_runner.return_value.run.assert_called_once_with(discover.return_value)
            run.assert_not_called()
            which.assert_not_called()


if __name__ == "__main__":
    unittest.main()
