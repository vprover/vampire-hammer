#!/usr/bin/env python3
"""Synchronize FO/HO starts and exercise cancellation and checked winners."""
import os
from pathlib import Path
import sys
import tempfile
import time

problem = sys.stdin.read()
args = sys.argv[1:]
stem = Path(sys.argv[0]).stem
root = Path("artifacts") / stem
stage = "ho" if problem.lstrip().startswith("thf(") else "fo"

root.with_suffix(f".{stage}.args").write_text(" ".join(args))
root.with_suffix(f".{stage}.started").write_text(str(os.getpid()))
other = root.with_suffix(f".{'fo' if stage == 'ho' else 'ho'}.started")
deadline = time.monotonic() + 5
if "serial" in stem and stage == "fo":
    print("% SZS status GaveUp")
    raise SystemExit(1)
if "serial" in stem:
    pid = int(other.read_text())
    try:
        os.kill(pid, 0)
    except ProcessLookupError:
        pass
    else:
        raise RuntimeError("single-processor searches overlapped")
while "serial" not in stem and not other.exists():
    if time.monotonic() > deadline:
        raise RuntimeError("FO and HO did not overlap")
    time.sleep(0.01)
print(f"% Parallel test args: {' '.join(args)}", file=sys.stderr, flush=True)

if "both-fail" in stem:
    print("% SZS status GaveUp")
    raise SystemExit(1)
if "bad-replay" in stem and stage == "ho":
    print("% SZS status Unsatisfiable\nthf(bogus,plain,$false,inference(unsupported,[],[])).")
    raise SystemExit(0)
if ("fo-wins" in stem and stage == "ho") or ("ho-wins" in stem and stage == "fo"):
    time.sleep(20)
    raise RuntimeError("losing search was not cancelled")
if "split" in stem:
    kind = "direct" if "&" in problem else "leaf"
    root.with_suffix(f".{kind}.{stage}.args").write_text(" ".join(args))
    # Verify both races received their allocations before allowing a winner.
    while not all(root.with_suffix(f".{attempt}.{route}.args").exists()
                  for attempt in ("direct", "leaf") for route in ("fo", "ho")):
        if time.monotonic() > deadline:
            raise RuntimeError("direct/split route allocations were not all observed")
        time.sleep(0.01)
    if "&" in problem:
        root.with_suffix(f".unsplit.{stage}.pid").write_text(str(os.getpid()))
        time.sleep(20)
        raise RuntimeError("unsplit search was not cancelled")
    while not any(root.with_suffix(f".unsplit.{route}.pid").exists() for route in ("fo", "ho")):
        if time.monotonic() > deadline:
            raise RuntimeError("decomposed and unsplit searches did not overlap")
        time.sleep(0.01)
binary = os.environ.get("VAMPIRE_BIN", str(Path(__file__).resolve().parents[3] / ".lake/vampire/build/vampire"))
# exec keeps the mock's PID: cancelling it also cancels the real prover.
with tempfile.TemporaryFile(mode="w+") as source:
    source.write(problem)
    source.seek(0)
    os.dup2(source.fileno(), 0)
    os.execv(binary, [binary, *args])
