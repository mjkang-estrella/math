#!/usr/bin/env python3
"""Write review-manifest.json for this directory and print its SHA256 (MIT)."""
import hashlib
import importlib.util
import json
from pathlib import Path

ROOT = Path(__file__).absolute().parent
spec = importlib.util.spec_from_file_location('review_verify', ROOT / 'verify.py')
verify = importlib.util.module_from_spec(spec)
spec.loader.exec_module(verify)

inv = verify.inventory(ROOT)
manifest = {
    'review': 't117q-formal-review-r1',
    'verdict': 'PASS_SCOPED_T117Q',
    'scope': 'scoped formal support only; no full-proof, contribution, manuscript, acceptance or count verdict',
    'packet_manifest_anchor': 'b741e2d76e9383238b5f3e975c634e2bb48b75eaa00dc1fb93371b0a1c139b37',
    'excludes_only': verify.MANIFEST,
    'files': inv['files'],
    'directories': inv['directories'],
}
raw = (json.dumps(manifest, indent=2) + '\n').encode()
(ROOT / verify.MANIFEST).write_bytes(raw)
print(hashlib.sha256(raw).hexdigest())
