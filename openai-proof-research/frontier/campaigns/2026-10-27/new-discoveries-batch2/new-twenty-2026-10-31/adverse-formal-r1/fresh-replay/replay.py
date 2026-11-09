"""Fail-closed replay of an incomplete research packet, NOT a proof replay."""
from pathlib import Path
import os,sys,json,hashlib
root=Path(__file__).resolve().parent
# Required future toolchain variables; never silently choose a toolchain.
lean=os.environ.get('LEAN_BIN');packages=os.environ.get('LEAN_PACKAGES')
if list(root.rglob('*.olean')):
 print('REFUSED: existing oleans');sys.exit(2)
for name,digest in json.loads((root/'PACKET-SOURCES.json').read_text()).items():
 p=root/name
 if not p.is_file() or hashlib.sha256(p.read_bytes()).hexdigest()!=digest:
  print('REFUSED: source hash mismatch: '+name);sys.exit(2)
if not list((root/'formal').glob('*.lean')):
 print('HOLD: no Lean sources; prior-art gate incomplete; no kernel replay, leanchecker or declaration audit possible')
 print('LEAN_BIN supplied:',bool(lean),'LEAN_PACKAGES supplied:',bool(packages));sys.exit(3)
print('REFUSED: this incomplete-packet driver does not implement a Lean replay');sys.exit(4)
