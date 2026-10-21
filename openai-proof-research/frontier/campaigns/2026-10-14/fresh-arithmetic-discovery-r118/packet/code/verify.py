"""Read-only exact-membership verifier. Supply all three detached envelope hashes."""
import argparse,hashlib,json,os,stat
from pathlib import Path

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
 files={};dirs=[];stack=[root]
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be nonsymlink directory')
 while stack:
  d=stack.pop()
  for e in os.scandir(d):
   p=Path(e.path);r=p.relative_to(root).as_posix();s=p.lstat()
   if stat.S_ISDIR(s.st_mode):dirs.append(r);stack.append(p)
   elif stat.S_ISREG(s.st_mode) and s.st_nlink==1:files[r]={'size':s.st_size,'sha256':digest(p)}
   else:raise ValueError('symlink/nonregular/hardlink: '+r)
 return files,sorted(dirs)
def verify(root,anchors):
 for name,expected in anchors.items():
  if len(expected)!=64 or digest(root/name)!=expected:raise ValueError('detached anchor mismatch: '+name)
 manifest=json.loads((root/'MANIFEST.json').read_text());files,dirs=inventory(root)
 if manifest.get('schema')!='r118-exact-v1':raise ValueError('schema')
 expected=manifest['files'];env=set(anchors)
 if set(expected)&env:raise ValueError('envelope in payload')
 if set(files)!=set(expected)|env:raise ValueError('file membership')
 if dirs!=manifest['directories']:raise ValueError('directory membership')
 for name,row in expected.items():
  if files[name]!=row:raise ValueError('payload mismatch: '+name)
 return {'files':len(files),'payload_files':len(expected),'directories':len(dirs),'read_only':True,'modes_bound':False}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('root',type=Path);a.add_argument('--final',required=True);a.add_argument('--manifest',required=True);a.add_argument('--report',required=True);x=a.parse_args()
 try:print(json.dumps(verify(x.root,{'FINAL.md':x.final,'MANIFEST.json':x.manifest,'REPORT.md':x.report}),sort_keys=True))
 except Exception as e:raise SystemExit('REJECT: '+str(e))
