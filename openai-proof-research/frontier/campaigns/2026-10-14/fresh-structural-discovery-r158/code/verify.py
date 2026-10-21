"""Read-only byte/membership verifier. Requires three independent detached anchors.
Usage: python verify.py ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256
No writes, no mathematical gates, no mode authentication.
"""
from pathlib import Path
import hashlib,json,os,stat,sys
ENVELOPES=('FINAL.md','MANIFEST.json','REPORT.md')
def digest(p): return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
 root=Path(root)
 if root.is_symlink() or not root.is_dir(): raise ValueError('invalid root')
 files={}; dirs=[]
 for base,children,names in os.walk(root,topdown=True,followlinks=False):
  for name in sorted(children):
   p=Path(base)/name; st=p.lstat()
   if not stat.S_ISDIR(st.st_mode) or p.is_symlink(): raise ValueError('invalid directory '+str(p))
   dirs.append(p.relative_to(root).as_posix())
  for name in sorted(names):
   p=Path(base)/name; st=p.lstat()
   if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1 or p.is_symlink(): raise ValueError('invalid file '+str(p))
   rel=p.relative_to(root).as_posix(); files[rel]={'size':st.st_size,'sha256':digest(p)}
 return dict(sorted(files.items())), sorted(dirs)
def verify(root,anchors):
 root=Path(root)
 if len(anchors)!=3 or any(len(a)!=64 or any(c not in '0123456789abcdef' for c in a) for a in anchors): raise ValueError('three SHA256 anchors required')
 files,dirs=inventory(root)
 for name,anchor in zip(ENVELOPES,anchors):
  if name not in files or files[name]['sha256']!=anchor: raise ValueError('detached anchor mismatch '+name)
 manifest=json.loads((root/'MANIFEST.json').read_text())
 if manifest.get('schema')!='r158-exact-payload-v1' or manifest.get('envelopes')!=list(ENVELOPES): raise ValueError('manifest schema mismatch')
 payload={k:v for k,v in files.items() if k not in ENVELOPES}
 if payload!=manifest['files']: raise ValueError('payload membership or byte mismatch')
 if dirs!=manifest['directories']: raise ValueError('directory membership mismatch')
 return {'files':len(payload),'directories':len(dirs),'envelopes':3,'artifact_only':True}
if __name__=='__main__':
 try:
  if len(sys.argv)!=5: raise ValueError(__doc__)
  print(json.dumps(verify(sys.argv[1],sys.argv[2:]),sort_keys=True))
 except Exception as exc:
  print('REJECT: '+str(exc),file=sys.stderr); sys.exit(1)
