#!/usr/bin/env python3
"""Check an extracted package's bytes and rerun its two algebra checkers.

This checks artifact integrity and finite calculations, not the PDE proof.
Use the documented lake commands separately for the supporting Lean proofs.
"""
from pathlib import Path, PurePosixPath
import hashlib
import json
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[4]
manifest = json.loads((ROOT / 'BUNDLE-MANIFEST.json').read_text())
for name, expected in manifest['files'].items():
    relative = PurePosixPath(name)
    if relative.is_absolute() or '..' in relative.parts:
        raise ValueError(f'Unsafe manifest path: {name}')
    path = ROOT / relative
    if path.is_symlink() or not path.resolve().is_relative_to(ROOT):
        raise ValueError(f'Nonregular package path: {name}')
    data = path.read_bytes()
    if len(data) != expected['bytes'] or hashlib.sha256(data).hexdigest() != expected['sha256']:
        raise ValueError(f'Package integrity mismatch: {name}')
print(f"Verified {len(manifest['files'])} project files", flush=True)
for relative in [
    'frontier/campaigns/2026-10-14/p-gradient-publication-v1/verify_editorial.py',
    'frontier/campaigns/2026-10-14/p-gradient-proof/checks/algebra_checks.py',
    'frontier/campaigns/2026-10-14/p-gradient-proof-r2/checks/r2_checks.py',
]:
    subprocess.run([sys.executable, '-I', str(ROOT / relative)], cwd=ROOT, check=True)
print('PASS: package integrity editorial equivalence and two algebra checkers; no analytic-proof certification')
