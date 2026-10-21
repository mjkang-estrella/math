#!/usr/bin/env python3
"""Read-only exact-membership verifier. Supply three independent SHA256 anchors.
This authenticates bytes/membership, not mathematical or contribution claims.
"""
import argparse,hashlib,json,os
from pathlib import Path,PurePosixPath

def digest(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={}
 if root.is_symlink():raise ValueError('root symlink')
 for base,dirs,names in os.walk(root,followlinks=False):
  for name in dirs:
   if (Path(base)/name).is_symlink():raise ValueError('directory symlink')
  for name in names:
   p=Path(base)/name
   if p.is_symlink() or not p.is_file():raise ValueError('nonregular payload')
   b=p.read_bytes();files[p.relative_to(root).as_posix()]={'size':len(b),'sha256':digest(b)}
 return files

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('root');p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args();root=Path(a.root)
 actual=inventory(root)
 for name,anchor in [('FINAL.md',a.final_sha256),('MANIFEST.json',a.manifest_sha256),('REPORT.md',a.report_sha256)]:
  if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):raise ValueError('invalid detached anchor')
  if actual.get(name,{}).get('sha256')!=anchor:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes())
 if m['excluded_envelopes']!=['FINAL.md','MANIFEST.json','REPORT.md']:raise ValueError('envelope policy')
 expected={}
 for row in m['files']:
  name=row['path'];q=PurePosixPath(name)
  if q.is_absolute() or '..' in q.parts or str(q)!=name or name in expected or name in m['excluded_envelopes']:raise ValueError('invalid/duplicate path')
  expected[name]={'size':row['size'],'sha256':row['sha256']}
 payload={k:v for k,v in actual.items() if k not in m['excluded_envelopes']}
 if set(payload)!=set(expected):raise ValueError('exact membership mismatch')
 if payload!=expected:raise ValueError('payload bytes mismatch')
 print(json.dumps({'integrity':'matched','payload_files':len(expected),'whole_root_files':len(actual),'read_only':True,'mathematical_gate':False}))
if __name__=='__main__':main()
