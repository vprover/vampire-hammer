#!/usr/bin/env python3
"""Record solver calls after a tiny FO mono window; never supply a proof."""
from pathlib import Path
import sys

problem = sys.stdin.read()
path = Path("artifacts/goal-decomposition/mono.calls")
path.parent.mkdir(parents=True, exist_ok=True)
with path.open("a") as calls:
    calls.write("ho\n" if "thf(" in problem else "fo\n")
print("% SZS status Timeout")
print("% Termination reason: Time limit")
sys.exit(1)
