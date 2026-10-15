#!/usr/bin/env python3
"""Count prover starts; optionally refuse every search to test cache hits."""
import os
from pathlib import Path
import sys

root = Path(__file__).resolve().parents[3]
with (root / "artifacts/session-cache.calls").open("a") as output:
    output.write("search\n")
if (root / "artifacts/session-cache.block").exists():
    print("% SZS status GaveUp")
    raise SystemExit(1)
binary = os.environ.get("VAMPIRE_BIN", str(root / ".lake/vampire/build/vampire"))
os.execv(binary, [binary, *sys.argv[1:]])
