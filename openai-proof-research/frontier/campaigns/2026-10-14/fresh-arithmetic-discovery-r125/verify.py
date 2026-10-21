"""Offline read-only exact-membership verifier. Requires three detached anchors.
Usage: python -B verify.py ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256
This checks artifacts only. It neither assigns mathematical gates nor repairs files.
"""
import hashlib,json,os,stat,sys
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
 files={};directories=[]
 for dp,ds,fs in os.walk(root,topdown=True,followlinks=False):
  here=Path(dp)
  for name in sorted(ds):
   p=here/name;st=p.lstat();rel=p.relative_to(root).as_posix()
   if not stat.S_ISDIR(st.st_mode) or p.is_symlink():raise ValueError('non-directory/symlink '+rel)
   directories.append(rel)
  for name in sorted(fs):
   p=here/name;st=p.lstat();rel=p.relative_to(root).as_posix()
   if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('non-regular or multiple links '+rel)
   if rel not in ENVELOPES:files[rel]={'size':st.st_size,'sha256':digest(p)}
 return {'files':dict(sorted(files.items())),'directories':sorted(directories)}
def verify(root,anchors):
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be real directory')
 for name,anchor in zip(['FINAL.md','MANIFEST.json','REPORT.md'],anchors):
  if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):raise ValueError('invalid detached anchor')
  p=root/name;st=p.lstat()
  if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('invalid envelope '+name)
  if digest(p)!=anchor:raise ValueError('detached anchor mismatch '+name)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m.get('schema')!='r125-exact-v1' or m.get('outside_payload_envelopes')!=sorted(ENVELOPES):raise ValueError('manifest schema')
 actual=inventory(root)
 if actual['files']!=m.get('files') or actual['directories']!=m.get('directories'):raise ValueError('exact payload membership or bytes mismatch')
 print('ACCEPT exact artifact membership:',len(actual['files']),'payload files,',len(actual['directories']),'directories; no mathematical gate')
if __name__=='__main__':
 try:
  if len(sys.argv)!=5:raise ValueError('require ROOT and three explicit detached SHA256 anchors')
  verify(Path(sys.argv[1]),sys.argv[2:])
 except Exception as e:
  print('REJECT',str(e));sys.exit(1)
