#!/usr/bin/env python3
"""Exercise HO -> FO -> HO slice transitions; the proving stage uses the real prover."""
import os
from pathlib import Path
import subprocess
import sys
import time

problem = sys.stdin.read()
args = sys.argv[1:]
limit = args[args.index('--time_limit') + 1]
stage = 'ho' if problem.lstrip().startswith('thf(') else 'fo'
mode = Path(sys.argv[0]).stem
alternate = '--func_ext' in args
print(f'% Slice test stage: {stage}; limit: {limit}; alternate: {alternate}; args: {" ".join(args)}', file=sys.stderr, flush=True)
# 'slices-fo': HO times out, FO proves. 'slices-ho-retry': HO times out, FO
# reports a model (early failure), the alternate-strategy HO run proves.
# 'slices-timeouts': every stage times out.
def timeout():
    time.sleep(0.2)
    print('% SZS status Timeout')
    print('% Termination reason: Time limit')
    print('% Time elapsed: 0.2 s')
    print('% Proof not found in time 0.2 s')
    raise SystemExit(1)
if 'timeouts' in mode:
    timeout()
if stage == 'ho' and not ('ho-retry' in mode and alternate):
    timeout()
if stage == 'fo' and 'ho-retry' in mode:
    print('% SZS status Satisfiable')
    raise SystemExit(0)
binary = os.environ.get('VAMPIRE_BIN', str(Path(__file__).resolve().parents[3] / '.lake/vampire/build/vampire'))
raise SystemExit(subprocess.run([binary, *args], input=problem, text=True).returncode)
