#!/usr/bin/env python3
"""Read-only exact-byte/membership check; no mathematical gate.
Checks regular files, rejects symlinks and multiply linked files. Does not
seal permissions, empty directories, timestamps, ownership or root mode.
"""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath

ENVELOPES=['FINAL.md','MANIFEST.json','REPORT.md']
def sha(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 files={}
 for base,dirs,names in os.walk(root,followlinks=False):
  for name in dirs:
   if (Path(base)/name).is_symlink():raise ValueError('directory symlink')
  for name in names:
   p=Path(base)/name;s=p.lstat()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('nonregular or linked file')
   b=p.read_bytes();files[p.relative_to(root).as_posix()]={'size':len(b),'sha256':sha(b)}
 return files
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('root')
 for x in ['final','manifest','report']:ap.add_argument('--'+x+'-sha256',required=True)
 a=ap.parse_args();root=Path(a.root);actual=inventory(root)
 for name,anchor in zip(ENVELOPES,[a.final_sha256,a.manifest_sha256,a.report_sha256]):
  if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):raise ValueError('invalid anchor')
  if actual.get(name,{}).get('sha256')!=anchor:raise ValueError('detached anchor mismatch '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes())
 if m['excluded_envelopes']!=ENVELOPES:raise ValueError('envelope policy')
 expected={}
 for row in m['files']:
  name=row['path'];p=PurePosixPath(name)
  if p.is_absolute() or '..' in p.parts or str(p)!=name or name in ENVELOPES or name in expected:raise ValueError('invalid membership')
  expected[name]={'size':row['size'],'sha256':row['sha256']}
 payload={k:v for k,v in actual.items() if k not in ENVELOPES}
 if payload!=expected:raise ValueError('payload/membership mismatch')
 print(json.dumps({'integrity':'matched','payload_files':len(payload),'whole_root_files':len(actual),'read_only':True,'mathematical_gate':False}))
if __name__=='__main__':main()
