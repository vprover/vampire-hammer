#!/usr/bin/env python3
"""Fail THF search; pass TFF input to the real prover for fallback tests."""
import os
from pathlib import Path
import subprocess
import sys

problem = sys.stdin.read()
limit = sys.argv[sys.argv.index('--time_limit') + 1]
if problem.lstrip().startswith('thf('):
    print(f'% Fallback test native search limit: {limit}')
    if 'test-timeout' in sys.argv:
        print('% SZS status Timeout')
        print('% Termination reason: Time limit')
        print('% Termination phase: Saturation')
    else:
        print('% SZS status GaveUp')
        print('% Termination reason: Refutation not found, incomplete strategy')
    raise SystemExit(1)

binary = os.environ.get('VAMPIRE_BIN', str(Path(__file__).resolve().parents[3] / '.lake/vampire/build/vampire'))
result = subprocess.run([binary, *sys.argv[1:]], input=problem, text=True)
raise SystemExit(result.returncode)
