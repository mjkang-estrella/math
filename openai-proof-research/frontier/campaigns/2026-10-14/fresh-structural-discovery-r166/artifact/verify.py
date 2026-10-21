#!/usr/bin/env python3
"""Read-only byte/membership verification; no mathematical or historical certificate."""
import argparse, hashlib, json, os, stat
from pathlib import Path
ENVELOPES={'FINAL.md','REPORT.md','MANIFEST.json'}
def sha(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def inventory(root):
 files={};dirs={'.':stat.S_IMODE(root.lstat().st_mode)}
 if not stat.S_ISDIR(root.lstat().st_mode):raise ValueError('root is not a real directory')
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for name in ds:
   p=Path(base)/name;st=p.lstat()
   if not stat.S_ISDIR(st.st_mode):raise ValueError('non-directory/symlink '+str(p))
   dirs[p.relative_to(root).as_posix()]=stat.S_IMODE(st.st_mode)
  for name in fs:
   p=Path(base)/name;st=p.lstat();rel=p.relative_to(root).as_posix()
   if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('nonregular/multilink '+rel)
   if rel in ENVELOPES:continue
   files[rel]={'size':st.st_size,'mode':stat.S_IMODE(st.st_mode),'sha256':sha(p)}
 return {'schema':'r166-exact-payload-v1','directories':dict(sorted(dirs.items())),'files':dict(sorted(files.items()))}
def verify(root,anchors):
 for name,expected in anchors.items():
  p=root/name;st=p.lstat()
  if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('bad envelope '+name)
  if len(expected)!=64 or sha(p)!=expected:raise ValueError('detached anchor mismatch '+name)
 with (root/'MANIFEST.json').open() as f:expected=json.load(f)
 observed=inventory(root)
 if observed!=expected:raise ValueError('payload membership/bytes/modes mismatch')
 return len(observed['files']),len(observed['directories'])
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('root',type=Path)
 for n in ['final','manifest','report']:p.add_argument('--'+n+'-sha256',required=True)
 a=p.parse_args();n,d=verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256})
 print(json.dumps({'artifact_only':'matched','payload_files':n,'directories_including_root':d,'writes':False}))
if __name__=='__main__':main()
