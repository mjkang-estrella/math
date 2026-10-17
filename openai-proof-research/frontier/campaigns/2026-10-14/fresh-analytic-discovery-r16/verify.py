#!/usr/bin/env python3
"""Read-only byte-integrity verification; not a proof or novelty verdict."""
import argparse, hashlib, json
from pathlib import Path, PurePosixPath
p=argparse.ArgumentParser();p.add_argument('--anchor',required=True);a=p.parse_args()
r=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
s=(r/'seal.json').read_bytes();assert sha(s)==a.anchor,'seal anchor mismatch'
seal=json.loads(s);m=(r/'manifest.json').read_bytes();assert sha(m)==seal['manifest_sha256']
manifest=json.loads(m);expected={};dirs=set()
for x in manifest['files']:
 n=x['path'];q=PurePosixPath(n)
 assert not q.is_absolute() and '..' not in q.parts and str(q)==n and n not in expected
 expected[n]=x
for n in manifest['directories']:
 q=PurePosixPath(n);assert not q.is_absolute() and '..' not in q.parts and str(q)==n and n not in dirs;dirs.add(n)
actual=set();actualdirs=set()
for q in r.rglob('*'):
 assert not q.is_symlink(),'symlink'
 n=q.relative_to(r).as_posix()
 if q.is_dir():actualdirs.add(n)
 else:actual.add(n)
assert actual==set(expected)|{'manifest.json','seal.json'},'file membership'
assert actualdirs==dirs,'directory membership'
for n,x in expected.items():
 b=(r/n).read_bytes();assert len(b)==x['bytes'] and sha(b)==x['sha256'],n
for name in ['source-identities.json','threshold-identities.json','radial-identities.json','radial-core-identities.json']:
 for x in json.loads((r/'inputs'/name).read_bytes()):
  b=(r/x['local']).read_bytes();blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
  assert blob==x['git_blob'],x['path']
f=json.loads((r/'freeze-receipt.json').read_bytes())
assert sha((r/'original-scope.md').read_bytes())==f['scope_sha256']
assert sha((r/'screening-before-freeze.md').read_bytes())==f['screen_sha256']
print(json.dumps({'integrity':'PASS','payload_files':len(expected),'directories':len(dirs),'mathematical_verdict':None,'contribution_verdict':None,'counted':False}))
