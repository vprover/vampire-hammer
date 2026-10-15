#!/usr/bin/env python3
"""Give up on the first HO strategy; run the real prover on the alternative."""
import os
from pathlib import Path
import subprocess
import sys

problem = sys.stdin.read()
if '--heur_inst' not in sys.argv:
    print('% SZS status GaveUp for retry-test')
    print('% Termination reason: Refutation not found, incomplete strategy')
    raise SystemExit(1)
print('% Retry arguments: ' + ' '.join(sys.argv[1:]), flush=True)
binary = os.environ.get('VAMPIRE_BIN', str(Path(__file__).resolve().parents[3] / '.lake/vampire/build/vampire'))
result = subprocess.run([binary, *sys.argv[1:]], input=problem, text=True)
raise SystemExit(result.returncode)
