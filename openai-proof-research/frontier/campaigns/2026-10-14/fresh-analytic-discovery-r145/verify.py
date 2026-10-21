#!/usr/bin/env python3
"""Read-only own-packet verifier. Detached anchors must be supplied explicitly."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,os,sys,fnmatch
p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
def digest(b):return hashlib.sha256(b).hexdigest()
def fail(msg):raise ValueError(msg)
peer_patterns=['*structural*r150*','*arithmetic*r114*','*structural*r151*','*arithmetic*r115*','*arithmetic*r116*']
def peer_guard(name):
 if any(fnmatch.fnmatchcase(name.lower(),pat) for pat in peer_patterns):fail('excluded peer path component')
try:
 R=Path(a.root).absolute(); anchors={'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256}
 if R.is_symlink():fail('root symlink')
 for name,h in anchors.items():
  if len(h)!=64 or any(c not in '0123456789abcdef' for c in h):fail('invalid detached anchor '+name)
  q=R/name
  if q.is_symlink() or not q.is_file() or digest(q.read_bytes())!=h:fail('detached anchor mismatch '+name)
 j=json.loads((R/'MANIFEST.json').read_text());expected={};rows=j['files']
 for row in rows:
  name=row['path'];pname=PurePosixPath(name)
  if pname.is_absolute() or '..' in pname.parts or str(pname)!=name or name in expected or name in anchors:fail('invalid/duplicate manifest member')
  expected[name]=row
 actual=set()
 for parent,dirs,files in os.walk(R,followlinks=False):
  for n in dirs+files:
   peer_guard(n)
   q=Path(parent)/n
   if q.is_symlink():fail('symlink '+str(q.relative_to(R)))
  for n in files:
   q=Path(parent)/n
   if not q.is_file():fail('nonregular member')
   actual.add(q.relative_to(R).as_posix())
 if actual!=set(expected)|set(anchors):fail('exact membership mismatch')
 for name,row in expected.items():
  b=(R/name).read_bytes()
  if len(b)!=row['size'] or digest(b)!=row['sha256']:fail('payload mismatch '+name)
 print(json.dumps({'integrity':'MATCH','payload_files':len(expected),'outside_envelopes':3,'writes':0,'mathematical_gate':False}))
except Exception as e:
 print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
