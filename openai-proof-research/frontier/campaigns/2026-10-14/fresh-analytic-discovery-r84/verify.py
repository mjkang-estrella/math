#!/usr/bin/env python3
import argparse, hashlib, json
from pathlib import Path
p=argparse.ArgumentParser();p.add_argument('--manifest-sha256',required=True);p.add_argument('--sources',action='store_true');a=p.parse_args()
r=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
b=(r/'manifest.json').read_bytes()
assert h(b)==a.manifest_sha256,'manifest anchor mismatch'
m=json.loads(b)
assert m['status']=='NO_NOMINEE' and m['scope_frozen'] is False and m['count_change']==0,'status mismatch'
for name,digest in m['files'].items():
 q=r/name;assert not q.is_symlink() and h(q.read_bytes())==digest,'payload mismatch: '+name
if a.sources:
 for x in json.loads((r/'source-receipts.json').read_text())['files']:
  b=(r/x['local']).read_bytes()
  assert h(b)==x['sha256'],'source SHA mismatch'
  assert hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()==x['git_blob'],'source blob mismatch'
 for x in json.loads((r/'primary-receipts.json').read_text()):
  assert h((r/x['local']).read_bytes())==x['sha256'],'primary mismatch'
print('PASS: checkpoint identity; no mathematical or novelty verdict')
