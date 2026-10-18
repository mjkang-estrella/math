#!/usr/bin/env python3
"""Writes review-manifest.json for this directory once (MIT). Refuses to overwrite."""
from pathlib import Path
import hashlib
import json
import sys

sys.dont_write_bytecode = True
ROOT = Path(__file__).absolute().parent
sys.path.insert(0, str(ROOT))
from verify import INPUT_ANCHOR, inventory  # noqa: E402

target = ROOT / 'review-manifest.json'
if target.exists():
    raise SystemExit('refusing to reseal: review-manifest.json exists')
files, dirs = inventory(ROOT)
manifest = {'schema': 'T027O-scoped-formal-review-r1', 'verdict': 'PASS_SCOPED_FORMAL_SUPPORT',
            'full_theorem_formalized': False, 'input_manifest_sha256': INPUT_ANCHOR,
            'files': files, 'directories': dirs}
data = (json.dumps(manifest, indent=2, sort_keys=True) + '\n').encode()
target.write_bytes(data)
print(hashlib.sha256(data).hexdigest())
