#!/usr/bin/env python3
"""Write MANIFEST.json for this review packet (run by the reviewer only). MIT."""
import hashlib, json, os
from pathlib import Path
root = Path(os.path.abspath(__file__)).parent
files = {}
for base, dirs, names in os.walk(root):
    dirs[:] = sorted(d for d in dirs if d != '__pycache__')
    for n in sorted(names):
        p = Path(base) / n
        rel = p.relative_to(root).as_posix()
        if rel == 'MANIFEST.json': continue
        b = p.read_bytes()
        files[rel] = {'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()}
m = {'schema': 'T298P-manuscript-review-r1', 'verdict': 'NEEDS_REVISION',
     'target_manifest_sha256': '24a3e405e1bceda384a8b6a4e28f610809a4c9ec5b32b0a66e0277b24b2124fe',
     'note': 'external anchor required; a hash stored here would not be one', 'files': dict(sorted(files.items()))}
(root / 'MANIFEST.json').write_text(json.dumps(m, indent=1) + '\n')
print(hashlib.sha256((root / 'MANIFEST.json').read_bytes()).hexdigest())
