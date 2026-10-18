#!/usr/bin/env python3
import argparse, hashlib, json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--manifest-sha256',required=True);p.add_argument('--dependencies',action='store_true');a=p.parse_args()
r=Path(__file__).absolute().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
b=(r/'manifest.json').read_bytes();assert sha(b)==a.manifest_sha256,'manifest anchor mismatch'
m=json.loads(b)
assert m['status']=='UNRESOLVED_FULL_TARGET' and not m['complete_proof'] and not m['nominee'] and m['count_change']==0,'status mismatch'
actual={p.relative_to(r).as_posix() for p in r.rglob('*') if p.is_file() and 'private' not in p.relative_to(r).parts and p.name!='manifest.json'}
assert actual==set(m['files']),'public membership mismatch'
for name,h in m['files'].items():
 q=r/name;assert q.is_file() and not q.is_symlink() and q.stat().st_nlink==1,'unsafe payload'
 assert sha(q.read_bytes())==h,'payload mismatch: '+name
s=json.loads((r/'scope-status.json').read_text());assert not s['complete_proof'] and not s['nominee'] and s['count_change']==0,'scope status mismatch'
if a.dependencies:
 repo=r.parents[3]
 for d in json.loads((r/'dependencies.json').read_text())['items']:
  assert sha((repo/d['path']).read_bytes())==d['sha256'],'dependency mismatch'
 d=json.loads((r/'new-source-receipt.json').read_text());b=(r/d['local']).read_bytes()
 assert sha(b)==d['sha256'],'source SHA mismatch'
 blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
 assert blob==d['git_blob'],'source blob mismatch'
 tree=json.loads((repo/'sources/preprints-tree.json').read_text())
 assert any(x['path']==d['path'] and x['sha']==blob for x in tree['tree']),'canonical membership mismatch'
print('PASS: unresolved checkpoint identity only')
