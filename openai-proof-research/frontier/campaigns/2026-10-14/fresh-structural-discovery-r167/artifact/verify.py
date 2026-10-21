"""Read-only artifact verification; requires three independently supplied anchors."""
import argparse,hashlib,json,os,stat
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={};dirs={'.':stat.S_IMODE(root.stat().st_mode)}
 for at,ds,fs in os.walk(root,followlinks=False):
  for name in ds:
   p=Path(at)/name;s=p.lstat()
   if not stat.S_ISDIR(s.st_mode):raise ValueError('non-directory or symlink: '+str(p))
   dirs[p.relative_to(root).as_posix()]=stat.S_IMODE(s.st_mode)
  for name in fs:
   p=Path(at)/name;rel=p.relative_to(root).as_posix();s=p.lstat()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('nonregular/multiple-link file: '+rel)
   if rel in ENVELOPES:continue
   b=p.read_bytes();files[rel]={'size':len(b),'sha256':sha(b),'mode':stat.S_IMODE(s.st_mode),'nlink':s.st_nlink}
 return {'files':dict(sorted(files.items())),'directories':dict(sorted(dirs.items()))}
def verify(root,anchors):
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 for name,anchor in anchors.items():
  p=root/name;s=p.lstat()
  if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('invalid envelope '+name)
  if sha(p.read_bytes())!=anchor:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes())
 if m.get('schema')!='r167-exact-payload-v1':raise ValueError('schema mismatch')
 actual=inventory(root)
 if actual!=m['payload']:raise ValueError('exact payload membership/bytes/mode mismatch')
 return {'artifact_only':'matched','files':len(actual['files']),'directories':len(actual['directories'])}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path)
 for flag in ('final','manifest','report'):p.add_argument('--'+flag,required=True)
 a=p.parse_args()
 try:print(json.dumps(verify(a.root,dict(zip(('FINAL.md','MANIFEST.json','REPORT.md'),(a.final,a.manifest,a.report)))),sort_keys=True))
 except Exception as e:print(json.dumps({'artifact_only':'rejected','reason':str(e)}));raise SystemExit(1)
