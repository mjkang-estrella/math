"""Read-only exact-payload verifier. Requires three independently supplied anchors.
Usage: python verify.py ROOT --final SHA256 --manifest SHA256 --report SHA256
Artifact integrity only; no mathematical verdict. Does not bind modes or timestamps.
"""
import argparse,hashlib,json,os,stat
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(b):return hashlib.sha256(b).hexdigest()
def regular(p):
 s=p.lstat()
 if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('not regular single-link: '+str(p))
def inventory(root):
 files={};dirs=[]
 if root.is_symlink() or not root.is_dir():raise ValueError('bad root')
 for here,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in ds:
   p=Path(here)/name
   if p.is_symlink() or not stat.S_ISDIR(p.lstat().st_mode):raise ValueError('bad directory '+str(p))
   dirs.append(p.relative_to(root).as_posix())
  for name in fs:
   p=Path(here)/name;regular(p);rel=p.relative_to(root).as_posix()
   if rel in ENVELOPES:continue
   b=p.read_bytes();files[rel]={'size':len(b),'sha256':digest(b)}
 return {'directories':sorted(dirs),'files':dict(sorted(files.items()))}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('root',type=Path)
 for x in ('final','manifest','report'):ap.add_argument('--'+x,required=True)
 a=ap.parse_args()
 for name,want in [('FINAL.md',a.final),('MANIFEST.json',a.manifest),('REPORT.md',a.report)]:
  p=a.root/name;regular(p)
  if len(want)!=64 or digest(p.read_bytes())!=want:raise ValueError('detached anchor mismatch '+name)
 expected=json.loads((a.root/'MANIFEST.json').read_text())
 if expected!=inventory(a.root):raise ValueError('exact membership/bytes mismatch')
 print('Artifact bytes and exact membership match; no mathematical gate.')
if __name__=='__main__':
 try:main()
 except Exception as e:raise SystemExit(str(e))
