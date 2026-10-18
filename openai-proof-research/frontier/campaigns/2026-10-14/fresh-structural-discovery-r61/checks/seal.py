#!/usr/bin/env python3
"""Author-side deterministic inventory creation; does not supply trust anchor."""
from pathlib import Path
import hashlib,json,stat
p=Path(__file__).absolute().parents[1]
files=[];dirs=['.']
for f in sorted(p.rglob('*')):
 s=f.lstat();rel=f.relative_to(p).as_posix()
 if stat.S_ISDIR(s.st_mode):dirs.append(rel)
 elif stat.S_ISREG(s.st_mode):
  assert s.st_nlink==1
  if rel!='MANIFEST.json':
   b=f.read_bytes();files.append({'path':rel,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 else:raise ValueError('nonregular node '+rel)
m={'schema':'strict-exact-inventory-v1','packet':'fresh-structural-discovery-r61','status':'Author-side T247G full candidate; no independent gate/count','directories':sorted(dirs),'files':files}
b=(json.dumps(m,indent=2)+'\n').encode();(p/'MANIFEST.json').write_bytes(b)
print(hashlib.sha256(b).hexdigest())
