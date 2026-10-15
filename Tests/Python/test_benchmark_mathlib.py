import importlib.util
import json
import os
from pathlib import Path
import tempfile
import unittest
from unittest.mock import patch


SCRIPT = Path(__file__).resolve().parents[2] / "Tests/scripts/benchmark-mathlib.py"
benchmark = None
if SCRIPT.is_file():
    spec = importlib.util.spec_from_file_location("benchmark_mathlib", SCRIPT)
    benchmark = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(benchmark)


@unittest.skipIf(benchmark is None, "Optional benchmark script is not included in this checkout")
class BenchmarkTests(unittest.TestCase):
    def test_resume_rejects_changed_vampire_binary(self):
        with tempfile.TemporaryDirectory() as temporary:
            binary = Path(temporary) / "vampire"
            binary.write_bytes(b"first build")
            config = {"vampire": str(binary), "vampire_sha256": benchmark.binary_hash(binary)}
            benchmark.verify_vampire_binary(config)
            binary.write_bytes(b"second build")
            with self.assertRaisesRegex(RuntimeError, "executable changed"):
                benchmark.verify_vampire_binary(config)
            with self.assertRaisesRegex(RuntimeError, "no Vampire binary fingerprint"):
                benchmark.verify_vampire_binary({"vampire": str(binary)})

    def test_sampling_balances_modules_and_is_reproducible(self):
        rows = [{"name": f"{module}.{index}", "module": module}
                for module in ("A", "B", "C") for index in range(20)]
        selected = benchmark.sample(rows, 8, "seed")
        self.assertEqual(selected, benchmark.sample(list(reversed(rows)), 8, "seed"))
        counts = [sum(row["module"] == module for row in selected) for module in ("A", "B", "C")]
        self.assertLessEqual(max(counts) - min(counts), 1)
        self.assertEqual(len({row["name"] for row in selected}), 8)

    def test_focused_selection_keeps_original_ids(self):
        with tempfile.TemporaryDirectory() as temporary:
            corpus = Path(temporary)
            rows = [{"id": 42, "name": "A"}, {"id": 105, "name": "B"}]
            (corpus / "lemmas.jsonl").write_text("".join(json.dumps(row) + "\n" for row in rows))
            names = corpus / "names.txt"
            names.write_text("B\nB\n")
            self.assertEqual(benchmark.select_from_corpus(corpus, names, 5000), [rows[1]])
            names.write_text("missing\n")
            with self.assertRaises(ValueError):
                benchmark.select_from_corpus(corpus, names, 5000)

    def test_search_budget_is_scoped_to_the_benchmark_case(self):
        source = benchmark.case_command({"id": 42, "name": "A"}, Path("run"), Path("events"), 20)
        self.assertTrue(source.startswith('set_option vampire.timeLimit 20 in\n'))
        self.assertIn('set_option vampire.outputPath "run/problems/00042.p" in\n', source)
        default = benchmark.case_command({"id": 42, "name": "A"}, Path("run"), Path("events"))
        self.assertTrue(default.startswith('set_option vampire.timeLimit 5 in\n'))

    def test_failure_categories_distinguish_search_and_replay(self):
        for message, expected in [
            ("Monomorphization failed because of a dependent type", "unsupported_input"),
            ("Auto.Reif.resolveTy :: Unable to resolve a dependent type", "unsupported_input"),
            ("Vampire timed out after 5 s", "search_timeout"),
            ("Vampire proof-search budget exhausted", "search_timeout"),
            ("Vampire aborted by signal SIGABRT on; no complete TSTP proof was produced.", "process_error"),
            ("Could not start Vampire executable `/missing`: file does not exist", "process_error"),
            ("Mock Vampire failed (2): initialization failure", "process_error"),
            ("Vampire did not produce a refutation (SZS status Satisfiable).", "search_unsuccessful"),
            ("Could not decode Vampire TPTP proof", "replay_error"),
            ("Could not parse Vampire output: malformed certificate", "replay_error"),
            ("Could not preprocess Vampire TSTP proof: unsupported higher-order step", "replay_error"),
            ("choice operator `s1` has an unsupported type or missing inhabitant", "replay_error"),
            ("difference witness requires function operands", "replay_error"),
            ("local replay expected `s1` to denote a lean-auto atom", "replay_error"),
            ("TPTP input step `f1` does not match local source fact `fact0`", "replay_error"),
        ]:
            self.assertEqual(benchmark.failure_kind({"status": "error", "error": message}), expected)

    def test_baseline_unsolved_goals_are_expected_search_failures(self):
        for prover, message in [('lean-auto-duper', 'Duper saturated'), ('duper', 'Duper saturated'), ('aesop', 'unsolved goals'),
                                ('simp_all', 'unsolved goals')]:
            self.assertEqual(benchmark.failure_kind({'status': 'error', 'prover': prover, 'error': message}),
                             'search_unsuccessful')

    def test_saved_query_variants_include_routed_and_retry_inputs_only(self):
        with tempfile.TemporaryDirectory() as temporary:
            problem = Path(temporary) / '00000.p'
            names = ('00000.p', '00000.p.branch-2.p', '00000.p.fo.p',
                     '00000.p.ho-first', '00000.p.fo-second',
                     '00000.p.branch-2.p.before-ho.fo-first')
            for name in names:
                (problem.parent / name).write_text('tff(a, axiom, p).\n')
            # These are artifacts attached to a query, never queries themselves.
            for suffix in ('.stdout', '.events.jsonl', '.fmb.stdout'):
                Path(str(problem) + suffix).write_text('diagnostic\n')
            self.assertEqual([path.name for path in benchmark.vampire_problem_files(problem)], [
                '00000.p', '00000.p.branch-2.p', '00000.p.fo.p',
                '00000.p.branch-2.p.before-ho.fo-first', '00000.p.fo-second', '00000.p.ho-first'])

    def test_lean_literals_preserve_supplementary_unicode(self):
        source = benchmark.case_command(
            {"id": 42, "name": "ContinuousLinearMap.extendTo𝕜'_apply"},
            Path("run-𝕜"), Path("events-𝕜"),
        )
        self.assertIn("ContinuousLinearMap.extendTo𝕜'_apply", source)
        self.assertIn('"run-𝕜/problems/00042.p"', source)
        self.assertNotIn("\\ud835", source)

    def test_unexpected_event_restarts_tail_without_accepting_foreign_result(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            (output / "chunks").mkdir()
            (output / "problems").mkdir()
            executable = output / "lake"
            executable.write_text('''#!/usr/bin/env python3
import json, pathlib, re, sys
source = pathlib.Path(next(a for a in sys.argv[1:] if a.endswith('.lean'))).read_text()
for name, events in re.findall(r'hammer_mathlib_try ("[^"\\n]+") recording ("[^"\\n]+")', source):
    name, events = json.loads(name), pathlib.Path(json.loads(events))
    if name == 'bad':
        name = '[anonymous]'
    with events.open('a') as stream:
        stream.write(json.dumps({'event': 'started', 'name': name}) + '\\n')
        stream.write(json.dumps({'event': 'finished', 'name': name, 'status': 'proved'}) + '\\n')
''')
            executable.chmod(0o700)
            recorded = []
            environment = {"PATH": str(output) + os.pathsep + os.environ["PATH"]}
            with patch.dict(os.environ, environment), patch.object(benchmark, "PROJECT", output):
                benchmark.run_chunk(
                    [{"id": 1, "name": "bad"}, {"id": 2, "name": "quick"}],
                    output, output / "unused-wrapper", 1, 0, recorded.append,
                )
            self.assertEqual([(row["name"], row["status"]) for row in recorded],
                             [("bad", "infrastructure_error"), ("quick", "proved")])
            self.assertIn("Unexpected benchmark event", recorded[0]["error"])
            self.assertEqual(len(list((output / "chunks").glob("*.lean"))), 2)

    def test_aborted_command_does_not_poison_later_results(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            (output / "chunks").mkdir()
            (output / "problems").mkdir()
            executable = output / "lake"
            executable.write_text('''#!/usr/bin/env python3
import json, pathlib, re, sys
source = pathlib.Path(next(a for a in sys.argv[1:] if a.endswith('.lean'))).read_text()
for name, events in re.findall(r'hammer_mathlib_try ("[^"\\n]+") recording ("[^"\\n]+")', source):
    name, events = json.loads(name), pathlib.Path(json.loads(events))
    with events.open('a') as stream:
        stream.write(json.dumps({'event': 'started', 'name': name}) + '\\n')
        if name != 'aborted':
            stream.write(json.dumps({'event': 'premises', 'name': name, 'premises': []}) + '\\n')
            stream.write(json.dumps({'event': 'proof_checked', 'name': name}) + '\\n')
            stream.write(json.dumps({'event': 'finished', 'name': name, 'status': 'proved'}) + '\\n')
sys.exit(1)
''')
            executable.chmod(0o700)
            recorded = []
            environment = {"PATH": str(output) + os.pathsep + os.environ["PATH"]}
            with patch.dict(os.environ, environment), patch.object(benchmark, "PROJECT", output):
                benchmark.run_chunk(
                    [{"id": 1, "name": "aborted"}, {"id": 2, "name": "quick"}],
                    output, output / "unused-wrapper", 1, 0, recorded.append,
                )
            self.assertEqual([(row["name"], row["status"]) for row in recorded],
                             [("aborted", "process_error"), ("quick", "proved")])
            self.assertEqual(len(list((output / "chunks").glob("*.lean"))), 1)

    def test_timeout_restarts_only_the_unattempted_tail(self):
        with tempfile.TemporaryDirectory() as temporary:
            output = Path(temporary)
            (output / "chunks").mkdir()
            (output / "problems").mkdir()
            executable = output / "lake"
            executable.write_text('''#!/usr/bin/env python3
import json, pathlib, re, sys, time
source = pathlib.Path(next(a for a in sys.argv[1:] if a.endswith('.lean'))).read_text()
for name, events in re.findall(r'hammer_mathlib_try ("[^"\\n]+") recording ("[^"\\n]+")', source):
    name, events = json.loads(name), pathlib.Path(json.loads(events))
    def write(event):
        with events.open('a') as stream:
            stream.write(json.dumps(event) + '\\n')
    write({'event': 'started', 'name': name})
    if name == 'hang':
        time.sleep(60)
    write({'event': 'finished', 'name': name, 'status': 'proved'})
''')
            executable.chmod(0o700)
            recorded = []
            environment = {"PATH": str(output) + os.pathsep + os.environ["PATH"]}
            with patch.dict(os.environ, environment), patch.object(benchmark, "PROJECT", output):
                benchmark.run_chunk(
                    [{"id": 1, "name": "hang"}, {"id": 2, "name": "quick"}],
                    output, output / "unused-wrapper", 0.05, 0, recorded.append, search_seconds=20,
                )
            self.assertEqual([(row["name"], row["status"]) for row in recorded],
                             [("hang", "timeout"), ("quick", "proved")])
            self.assertTrue((output / "chunks/chunk-0000-01.lean").exists())
            for chunk in (output / "chunks").glob("*.lean"):
                self.assertIn('set_option vampire.timeLimit 20 in\n', chunk.read_text())


if __name__ == "__main__":
    unittest.main()
