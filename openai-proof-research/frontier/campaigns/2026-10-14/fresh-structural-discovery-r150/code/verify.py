"""Read-only integrity verifier. No network, regeneration, imports of packet code, or writes."""
from pathlib import Path
import argparse,hashlib,json,os,stat
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inspect(root):
 if not stat.S_ISDIR(root.lstat().st_mode):raise ValueError('root not ordinary directory')
 files={};dirs={''}
 for base,children,names in os.walk(root,followlinks=False):
  for name in children:
   p=Path(base)/name;s=p.lstat()
   if not stat.S_ISDIR(s.st_mode):raise ValueError('nonordinary directory '+str(p))
   dirs.add(p.relative_to(root).as_posix())
  for name in names:
   p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('nonordinary/hardlinked file '+rel)
   files[rel]={'size':s.st_size,'sha256':digest(p)}
 return files,sorted(dirs)
def verify(root,anchors):
 files,dirs=inspect(root)
 for name,sha in anchors.items():
  if len(sha)!=64 or files.get(name,{}).get('sha256')!=sha:raise ValueError('detached anchor '+name)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m['schema']!='r150-exact-payload-v1':raise ValueError('schema')
 if m['envelopes']!=sorted(ENVELOPES):raise ValueError('envelopes')
 actual={k:v for k,v in files.items() if k not in ENVELOPES}
 if actual!=m['payload']:raise ValueError('payload membership/hash/size')
 if dirs!=m['directories']:raise ValueError('directory membership')
 return {'payloads':len(actual),'whole_root_files':len(files),'directories_including_root':len(dirs),'integrity_only':True}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('root',type=Path)
 for key in ['final','manifest','report']:p.add_argument('--'+key,required=True)
 a=p.parse_args()
 try:print(json.dumps(verify(a.root,{'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.md':a.report}),sort_keys=True))
 except (ValueError,KeyError,OSError,json.JSONDecodeError) as e:print('REJECT:',e);raise SystemExit(1)
