#!/usr/bin/env python3
"""Read-only exact packet membership; three REQUIRED detached SHA256 anchors."""
import argparse,hashlib,json,os,stat,sys
from pathlib import Path

def digest(b):return hashlib.sha256(b).hexdigest()
def verify(root,anchors):
 root=Path(root)
 assert root.is_dir() and not root.is_symlink(),'invalid root'
 for name,expected in anchors.items():
  p=root/name;s=p.lstat()
  assert stat.S_ISREG(s.st_mode) and s.st_nlink==1,'bad envelope type'
  assert len(expected)==64 and digest(p.read_bytes())==expected,'detached anchor mismatch: '+name
 m=json.loads((root/'MANIFEST.json').read_text());assert m['schema']=='r116-exact-payload-v1'
 files={};dirs=[]
 for base,ds,fs in os.walk(root,followlinks=False):
  for n in ds:
   p=Path(base)/n;s=p.lstat();assert stat.S_ISDIR(s.st_mode) and not p.is_symlink(),'bad directory type';dirs.append(p.relative_to(root).as_posix())
  for n in fs:
   p=Path(base)/n;s=p.lstat();assert stat.S_ISREG(s.st_mode) and s.st_nlink==1,'bad file type/link';rel=p.relative_to(root).as_posix()
   if rel in anchors:continue
   b=p.read_bytes();files[rel]={'size':len(b),'sha256':digest(b)}
 assert sorted(dirs)==m['directories'],'directory membership mismatch'
 assert files==m['files'],'payload membership/content mismatch'
 assert all(p.startswith('packet/') and '..' not in Path(p).parts for p in files),'invalid payload path'
 return {'verified_payload_files':len(files),'verified_directories':len(dirs),'envelopes':3,'mathematical_gate':False}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('root');ap.add_argument('--final',required=True);ap.add_argument('--manifest',required=True);ap.add_argument('--report',required=True);a=ap.parse_args()
 try:print(json.dumps(verify(a.root,{'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.md':a.report}),sort_keys=True))
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
