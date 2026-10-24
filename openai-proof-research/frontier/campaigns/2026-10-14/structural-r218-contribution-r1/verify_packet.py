"""Read-only own exact-selection verifier. Three detached anchors are required.
The manifest describes only this review's own files, never an inherited packet.
MANIFEST.json, REPORT.md, ANCHORS.json and root artifact-controls/ are excluded.
"""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def selected(root):
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 fs=[];ds=[]
 for base,dirs,files in os.walk(root,topdown=True,followlinks=False):
  rel=Path(base).relative_to(root)
  dirs[:]=[d for d in dirs if not (rel==Path('.') and d=='artifact-controls')]
  for name in dirs:
   p=Path(base)/name
   if p.is_symlink():raise ValueError('symlink directory')
   ds.append(p.relative_to(root).as_posix())
  for name in files:
   p=Path(base)/name;r=p.relative_to(root).as_posix()
   if r in {'MANIFEST.json','REPORT.md','ANCHORS.json'}:continue
   if p.is_symlink() or not stat.S_ISREG(p.lstat().st_mode):raise ValueError('nonregular selected file')
   fs.append(r)
 return sorted(fs),sorted(ds)
def verify(root,final_sha,manifest_sha,report_sha):
 for name,sha in [('FINAL.md',final_sha),('MANIFEST.json',manifest_sha),('REPORT.md',report_sha)]:
  p=root/name
  if p.is_symlink() or digest(p)!=sha:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes());fs,ds=selected(root)
 if fs!=sorted(m['files']) or ds!=sorted(m['directories']):raise ValueError('exact selection mismatch')
 if stat.S_IMODE(root.stat().st_mode)!=int(m['root_mode'],8):raise ValueError('root mode mismatch')
 for rel,d in m['files'].items():
  q=PurePosixPath(rel)
  if q.is_absolute() or '..' in q.parts or q.as_posix()!=rel:raise ValueError('unsafe selected path')
  p=root/rel
  if p.stat().st_size!=d['bytes'] or digest(p)!=d['sha256']:raise ValueError('selected bytes mismatch: '+rel)
  if stat.S_IMODE(p.stat().st_mode)!=int(d['mode'],8):raise ValueError('selected mode mismatch: '+rel)
 for rel,mo in m['directories'].items():
  q=PurePosixPath(rel)
  if q.is_absolute() or '..' in q.parts:raise ValueError('unsafe directory path')
  if stat.S_IMODE((root/rel).stat().st_mode)!=int(mo,8):raise ValueError('directory mode mismatch: '+rel)
 return len(fs),len(ds)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--final-sha',required=True);p.add_argument('--manifest-sha',required=True);p.add_argument('--report-sha',required=True);a=p.parse_args()
 f,d=verify(Path(a.root),a.final_sha,a.manifest_sha,a.report_sha)
 print(f'PASS: three explicit detached anchors; exact own selection {f} files/{d} directories; bytes and modes; read-only verification.')
