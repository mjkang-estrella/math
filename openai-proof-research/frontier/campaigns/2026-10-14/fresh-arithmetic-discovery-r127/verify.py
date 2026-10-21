#!/usr/bin/env python3
"""Read-only exact-membership verifier. Supply all three independent detached anchors."""
import argparse,hashlib,json,os,stat
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
 files={};dirs=[]
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in ds:
   p=Path(base)/name
   if not stat.S_ISDIR(p.lstat().st_mode) or p.is_symlink():raise ValueError('non-directory/symlink: '+str(p))
   dirs.append(p.relative_to(root).as_posix())
  for name in fs:
   p=Path(base)/name;rel=p.relative_to(root).as_posix();st=p.lstat()
   if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('not single-link regular: '+rel)
   if rel in ENVELOPES:continue
   b=p.read_bytes();files[rel]={'size':len(b),'sha256':digest(b)}
 return {'format':'r127-exact-membership-v1','directories':sorted(dirs),'files':dict(sorted(files.items()))}
def main():
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True)
 for s in ['final','manifest','report']:ap.add_argument('--'+s+'-sha256',required=True)
 a=ap.parse_args();root=Path(a.root)
 if root.is_symlink():raise ValueError('symlink root')
 for name,anchor in [('FINAL.md',a.final_sha256),('MANIFEST.json',a.manifest_sha256),('REPORT.md',a.report_sha256)]:
  p=root/name;st=p.lstat()
  if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('bad envelope: '+name)
  if digest(p.read_bytes())!=anchor:raise ValueError('detached anchor mismatch: '+name)
 recorded=json.loads((root/'MANIFEST.json').read_text())
 actual=inventory(root)
 if recorded!=actual:raise ValueError('exact payload membership/bytes mismatch')
 print('Artifact bytes and membership match supplied detached anchors; no mathematical verdict.')
if __name__=='__main__':
 try:main()
 except (OSError,ValueError) as e:raise SystemExit(str(e))
