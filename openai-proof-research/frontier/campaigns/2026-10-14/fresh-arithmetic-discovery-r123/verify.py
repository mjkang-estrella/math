#!/usr/bin/env python3
"""Read-only artifact verifier. Detached anchors are mandatory; no math verdict."""
import argparse,hashlib,json,os,stat
from pathlib import Path
ENV={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def verify(root,anchors):
 root=Path(root)
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
 for name in ENV:
  p=root/name;s=p.lstat()
  if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('envelope kind/link: '+name)
  if sha(p.read_bytes())!=anchors[name]:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes())
 if m.get('schema')!=1 or set(m.get('envelopes',[]))!=ENV:raise ValueError('manifest schema')
 expected=m['files'];actual={};dirs=[]
 for here,dd,ff in os.walk(root,followlinks=False):
  for name in dd:
   p=Path(here)/name;s=p.lstat()
   if not stat.S_ISDIR(s.st_mode):raise ValueError('non-directory: '+str(p))
   dirs.append(p.relative_to(root).as_posix())
  for name in ff:
   p=Path(here)/name;r=p.relative_to(root).as_posix();s=p.lstat()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('non-regular/multilink: '+r)
   if r in ENV:continue
   b=p.read_bytes();actual[r]={'size':len(b),'sha256':sha(b)}
 if actual!=expected:raise ValueError('payload membership, size or digest mismatch')
 if sorted(dirs)!=m['directories']:raise ValueError('directory membership mismatch')
 return {'payload_files':len(actual),'directories':len(dirs),'envelopes':3}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('root');a.add_argument('--final-sha256',required=True);a.add_argument('--manifest-sha256',required=True);a.add_argument('--report-sha256',required=True);v=a.parse_args()
 try:
  result=verify(v.root,{'FINAL.md':v.final_sha256,'MANIFEST.json':v.manifest_sha256,'REPORT.md':v.report_sha256})
 except Exception as e:print('REJECT:',e);raise SystemExit(1)
 print(json.dumps({'artifact_verification':'accept',**result},sort_keys=True))
