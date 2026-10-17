#!/usr/bin/env python3
"""Read-only receipt verification. First argument must be parent-held SHA256."""
from pathlib import Path
import hashlib, json, sys
root=Path(__file__).resolve().parent
assert len(sys.argv)==2 and len(sys.argv[1])==64, "Require external receipt SHA256"
raw=(root/'receipt.json').read_bytes()
assert hashlib.sha256(raw).hexdigest()==sys.argv[1], "Receipt anchor mismatch"
d=json.loads(raw)
rows=d['files']; names=[r['path'] for r in rows]
assert len(names)==len(set(names))
for name in names:
    q=Path(name)
    assert not q.is_absolute() and '..' not in q.parts and q.as_posix()==name
actual=[]; dirs=[]
for p in root.rglob('*'):
    assert not p.is_symlink(), "Symlink"
    if p.is_dir(): dirs.append(p.relative_to(root).as_posix())
    elif p.is_file() and p!=root/'receipt.json': actual.append(p.relative_to(root).as_posix())
assert sorted(actual)==sorted(names), "File membership mismatch"
assert sorted(dirs)==d['directories'], "Directory membership mismatch"
for row in rows:
    b=(root/row['path']).read_bytes()
    assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256'], row['path']
print('Verified exact receipt:',len(rows),'files;',len(dirs),'directories. No mathematical verdict.')
