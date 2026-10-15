# Contributor notes

Build with `lake build`. Run Lean files with `lake lean FILE` to load the
compiled tactic modules.

```sh
python3 Tests/run-tests.py
python3 Tests/run-tests.py --suite python
```

The default Lean suite uses fixtures. `--suite python` discovers Python tests
in `Tests/Python/`. `--suite all` runs Python and all
Lean regressions. Use `--vampire /path/to/vampire`
to select another certificate-emitting build. Use `--list` or positional
test paths for focused runs.