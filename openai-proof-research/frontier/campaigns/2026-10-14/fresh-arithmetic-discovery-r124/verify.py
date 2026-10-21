#!/usr/bin/env python3
"""Read-only exact-membership verifier. Detached anchors are mandatory."""
import argparse,hashlib,json,os,stat,sys
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 files={};dirs=[]
 for parent,ds,fs in os.walk(root,topdown=True,followlinks=False):
  ds.sort();fs.sort()
  for name in ds:
   p=Path(parent)/name;s=p.lstat()
   if not stat.S_ISDIR(s.st_mode):raise ValueError('non-directory or symlink: '+str(p))
   dirs.append(p.relative_to(root).as_posix())
  for name in fs:
   p=Path(parent)/name;s=p.lstat();rel=p.relative_to(root).as_posix()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('nonregular/multilink: '+rel)
   b=p.read_bytes();files[rel]={'size':len(b),'sha256':sha(b)}
 return files,sorted(dirs)
def main():
 a=argparse.ArgumentParser();a.add_argument('root',type=Path)
 for x in ['final','manifest','report']:a.add_argument('--'+x+'-sha256',required=True)
 ns=a.parse_args();files,dirs=inventory(ns.root)
 for name,key in [('FINAL.md','final'),('MANIFEST.json','manifest'),('REPORT.md','report')]:
  expected=getattr(ns,key+'_sha256')
  if len(expected)!=64 or any(c not in '0123456789abcdef' for c in expected):raise ValueError('invalid detached anchor')
  if name not in files or files[name]['sha256']!=expected:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((ns.root/'MANIFEST.json').read_bytes())
 if m.get('format')!='r124-exact-v1' or m.get('outside_envelopes')!=sorted(ENVELOPES):raise ValueError('unsupported manifest')
 payload={k:v for k,v in files.items() if k not in ENVELOPES}
 if payload!=m.get('files'):raise ValueError('file membership/size/hash mismatch')
 if dirs!=m.get('directories'):raise ValueError('directory membership mismatch')
 print(json.dumps({'artifact_verification':'accepted','payload_files':len(payload),'directories':len(dirs),'outside_envelopes':3,'mathematical_gate':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
