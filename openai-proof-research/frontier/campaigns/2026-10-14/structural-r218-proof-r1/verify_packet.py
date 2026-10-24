"""Read-only verifier for THIS root's exact selection. No inherited manifest.
Explicit detached FINAL, MANIFEST and outside REPORT anchors are mandatory.
Excludes only root MANIFEST.json, REPORT.md, ANCHORS.json and artifact-controls/.
The exclusions are not a permission to substitute a reduced selected packet.
"""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath
OUTSIDE={'MANIFEST.json','REPORT.md','ANCHORS.json'}
def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def inventory(root):
 files=[];dirs=[]
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  rel=Path(base).relative_to(root)
  ds[:]=[d for d in ds if not (rel==Path('.') and d=='artifact-controls')]
  for n in ds:
   p=Path(base)/n
   if p.is_symlink():raise ValueError('symlink directory')
   dirs.append(p.relative_to(root).as_posix())
  for n in fs:
   p=Path(base)/n;s=p.relative_to(root).as_posix()
   if s in OUTSIDE:continue
   if p.is_symlink() or not p.is_file():raise ValueError('nonregular selected file')
   files.append(s)
 return sorted(files),sorted(dirs)
def verify(root,final_sha,manifest_sha,report_sha):
 for name,expected in [('FINAL.md',final_sha),('MANIFEST.json',manifest_sha),('REPORT.md',report_sha)]:
  p=root/name
  if p.is_symlink() or not p.is_file():raise ValueError('invalid anchored file: '+name)
  if digest(p)!=expected:raise ValueError('detached anchor mismatch: '+name)
  if stat.S_IMODE(p.stat().st_mode)!=0o444:raise ValueError('anchor mode mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes())
 if m['format']!='structural218-proof-r1-exact-v1':raise ValueError('wrong manifest format')
 if stat.S_IMODE(root.stat().st_mode)!=int(m['root_mode'],8):raise ValueError('root mode mismatch')
 fs,ds=inventory(root)
 if fs!=sorted(m['files']) or ds!=sorted(m['directories']):raise ValueError('exact selection mismatch')
 for n,e in m['files'].items():
  q=PurePosixPath(n)
  if q.is_absolute() or '..' in q.parts or q.as_posix()!=n:raise ValueError('unsafe path')
  p=root/n
  if p.stat().st_size!=e['bytes'] or digest(p)!=e['sha256']:raise ValueError('selected bytes mismatch: '+n)
  if stat.S_IMODE(p.stat().st_mode)!=int(e['mode'],8):raise ValueError('selected mode mismatch: '+n)
 for n,mode in m['directories'].items():
  if stat.S_IMODE((root/n).stat().st_mode)!=int(mode,8):raise ValueError('directory mode mismatch: '+n)
 return {'files':len(fs),'directories':len(ds),'root_mode':m['root_mode'],'anchors':'all three supplied anchors match','read_only':True}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--final-sha',required=True);p.add_argument('--manifest-sha',required=True);p.add_argument('--report-sha',required=True);a=p.parse_args()
 print(json.dumps(verify(Path(a.root),a.final_sha,a.manifest_sha,a.report_sha),sort_keys=True))
