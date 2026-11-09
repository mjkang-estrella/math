#!/usr/bin/env python3
"""Rebuild the two certificates without modifying shared dependencies."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parent.parent

for candidate in ('fair-discrepancy-340783', 'permutation-spectrum-362146'):
    formal = ROOT/candidate/'formal'
    result = subprocess.run([sys.executable, str(formal/'rebuild.py')],
                            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT)
    (formal/'build/rebuild.log').write_text(result.stdout)
    if result.returncode:
        print(result.stdout)
        raise SystemExit(result.returncode)
    print(result.stdout.splitlines()[-1])

subprocess.run([sys.executable, str(ROOT/'verification/independent_checks.py')], check=True)
