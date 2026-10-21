#!/usr/bin/env python3
"""Read-only verification using externally supplied detached anchors."""
import argparse, hashlib, json, stat
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.json','ANCHORS.json'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(root,anchors):
 root=Path(root).resolve()
 for name,value in anchors.items():
  if len(value)!=64 or any(c not in '0123456789abcdef' for c in value):raise ValueError('invalid detached anchor')
  if digest(root/name)!=value:raise ValueError('detached anchor mismatch: '+name)
 manifest=json.loads((root/'MANIFEST.json').read_text())
 listed={x['path']:x for x in manifest['files']}
 if len(listed)!=len(manifest['files']):raise ValueError('duplicate payload path')
 actual=set()
 for p in root.rglob('*'):
  if p.is_symlink():raise ValueError('symlink in packet')
  if p.is_file():
   rel=p.relative_to(root).as_posix()
   if rel not in ENVELOPES:actual.add(rel)
 if actual!=set(listed):raise ValueError('payload coverage mismatch')
 for rel,entry in listed.items():
  p=root/rel
  if Path(rel).is_absolute() or '..' in Path(rel).parts:raise ValueError('unsafe payload path')
  if p.stat().st_size!=entry['bytes'] or digest(p)!=entry['sha256']:raise ValueError('payload mismatch: '+rel)
  if stat.S_IMODE(p.stat().st_mode)!=entry['mode']:raise ValueError('mode mismatch: '+rel)
 report=json.loads((root/'REPORT.json').read_text())
 if report['final_sha256']!=anchors['FINAL.md'] or report['manifest_sha256']!=anchors['MANIFEST.json']:raise ValueError('report binding mismatch')
 if report['payload_count']!=len(listed):raise ValueError('report count mismatch')
 return len(listed)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True);a=p.parse_args()
 try:
  n=verify(a.root,{'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.json':a.report})
  print(json.dumps({'artifact_check':'matched','payload_count':n,'writes':0,'mathematical_gate':False}))
 except Exception as e:
  print(json.dumps({'artifact_check':'rejected','reason':str(e),'writes':0}));raise SystemExit(1)
