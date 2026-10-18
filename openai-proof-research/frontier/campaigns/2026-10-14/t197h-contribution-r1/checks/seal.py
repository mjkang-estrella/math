#!/usr/bin/env python3
"""MIT. Writes MANIFEST.json for this review directory. Run once, before handoff; never on a received packet."""
import hashlib, json, sys
from pathlib import Path

root = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(root))
import verify  # noqa: E402

verify.ancestors_ok(root)
files, dirs = verify.scan(root)
files = [f for f in files if f != 'MANIFEST.json']
entries = []
for f in files:
    b = (root / f).read_bytes()
    entries.append({'path': f, 'bytes': len(b), 'sha256': hashlib.sha256(b).hexdigest()})
(root / 'MANIFEST.json').write_text(json.dumps({'files': entries, 'directories': dirs}, indent=2) + '\n')
print(hashlib.sha256((root / 'MANIFEST.json').read_bytes()).hexdigest())
