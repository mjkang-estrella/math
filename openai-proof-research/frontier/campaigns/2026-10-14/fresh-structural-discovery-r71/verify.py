#!/usr/bin/env python3
"""Read-only checkpoint verifier; requires externally supplied manifest anchor."""
import argparse,hashlib,json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);a=p.parse_args()
r=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
b=(r/'MANIFEST.json').read_bytes()
assert h(b)==a.anchor,'external manifest anchor mismatch'
m=json.loads(b);assert m['kind']=='author research checkpoint; no candidate'
files={str(x.relative_to(r)) for x in r.rglob('*') if x.is_file() and x.name!='MANIFEST.json'}
assert not any(x.is_symlink() for x in r.rglob('*')),'symlink forbidden'
assert files==set(m['files']),'membership mismatch'
for n,v in m['files'].items():
 b=(r/n).read_bytes();assert len(b)==v['bytes'] and h(b)==v['sha256'],n
s=json.loads((r/'source-receipt.json').read_text())
for e in s['sources']:
 b=(r/'private'/e['path']).read_bytes()
 assert h(b)==e['sha256']
 assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==e['git_blob']
print(json.dumps({'status':'PASS','payloads':len(files),'source_blobs':len(s['sources']),'limits':'Identity checks only; no independent mathematical review.'}))
