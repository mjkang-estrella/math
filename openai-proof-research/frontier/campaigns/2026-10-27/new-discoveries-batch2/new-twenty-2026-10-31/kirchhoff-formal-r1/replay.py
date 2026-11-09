#!/usr/bin/env python3
"""Diagnostic HOLD packet. A successful arithmetic run is not a formal replay."""
import os,sys,subprocess,json
from pathlib import Path
D=Path(__file__).resolve().parent
if any(D.rglob('*.olean')):
 print('Refusing existing oleans.',file=sys.stderr);sys.exit(2)
if '--exact-only' in sys.argv:
 r=subprocess.run([sys.executable,'-I',str(D/'scripts/gate.py')],cwd=D,env={'PATH':os.environ.get('PATH',''),'MALLOC_ARENA_MAX':'2','PYTHONDONTWRITEBYTECODE':'1'},timeout=140)
 sys.exit(r.returncode)
lean=os.environ.get('LEAN_BIN');packages=os.environ.get('LEAN_PACKAGES')
if not lean or not packages:
 print('Set LEAN_BIN and LEAN_PACKAGES for formal replay. This HOLD packet has no Lean endpoint.',file=sys.stderr)
 sys.exit(3)
print('FORMAL REPLAY NOT AVAILABLE: fidelity/prior-art gate unresolved; no Lean declarations. No leanchecker or audit success.',file=sys.stderr)
sys.exit(3)
