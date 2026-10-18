#!/usr/bin/env python3
"""Author-side inventory writer, not part of read-only verification. MIT."""
from pathlib import Path
import hashlib,json,stat
r=Path(__file__).resolve().parents[1];files={};dirs=[]
for p in sorted(r.rglob('*')):
 s=p.lstat();n=p.relative_to(r).as_posix()
 if stat.S_ISDIR(s.st_mode):dirs.append(n)
 elif stat.S_ISREG(s.st_mode) and s.st_nlink==1:
  if n!='MANIFEST.json':files[n]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':s.st_size}
 else:raise SystemExit('invalid node '+n)
m={'format':'rcs128-exact-inventory-v1','status':'AUTHOR_SIDE_MANUSCRIPT_PENDING_INDEPENDENT_REVIEW','files':files,'directories':dirs}
p=r/'MANIFEST.json';p.write_text(json.dumps(m,indent=2,sort_keys=True)+'\n');print(hashlib.sha256(p.read_bytes()).hexdigest())
