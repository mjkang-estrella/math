#!/usr/bin/env python3
"""Verify the exact payload inventory against the external seal. MIT."""
from pathlib import Path
import hashlib
import json

base = Path(__file__).resolve().parent
seal = json.loads((base.parent / 'seal.json').read_text())
actual = []
for path in sorted(base.rglob('*')):
    if path.is_symlink():
        raise AssertionError(f'Unexpected symlink: {path}')
    if path.is_file():
        raw = path.read_bytes()
        actual.append({'path': str(path.relative_to(base)), 'bytes': len(raw),
                       'sha256': hashlib.sha256(raw).hexdigest()})
assert actual == seal['inventory'], 'Payload inventory differs from external seal'
canonical = json.dumps(actual, sort_keys=True, separators=(',', ':')).encode()
digest = hashlib.sha256(canonical).hexdigest()
assert digest == seal['inventory_sha256']
print(json.dumps({'status': 'EXACT_INVENTORY_VERIFIED', 'files': len(actual),
                  'inventory_sha256': digest}, indent=2))
