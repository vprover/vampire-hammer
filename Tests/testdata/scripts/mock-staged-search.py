#!/usr/bin/env python3
"""Exercise staged-search transitions; successful stages use the real prover."""
import os
from pathlib import Path
import subprocess
import sys
import time

problem = sys.stdin.read()
args = sys.argv[1:]
limit = args[args.index('--time_limit') + 1]
stage = 'sat' if 'fmb' in args else 'ho' if problem.lstrip().startswith('thf(') else 'fo'
mode = Path(sys.argv[0]).stem
print(f'% Staged test stage: {stage}; limit: {limit}', file=sys.stderr, flush=True)
if stage == 'sat':
    print('% SZS status Satisfiable' if 'satisfiable' in mode else '% SZS status Unknown')
    raise SystemExit(0)
if stage == 'fo' and 'fo-success' not in mode:
    # Use a measurable part of the FO allowance so HO's remaining budget
    # can be distinguished from a fresh full search budget.
    time.sleep(0.2)
    print('% SZS status Timeout')
    print('% Termination reason: Time limit')
    raise SystemExit(1)
binary = os.environ.get('VAMPIRE_BIN', str(Path(__file__).resolve().parents[3] / '.lake/vampire/build/vampire'))
raise SystemExit(subprocess.run([binary, *args], input=problem, text=True).returncode)
