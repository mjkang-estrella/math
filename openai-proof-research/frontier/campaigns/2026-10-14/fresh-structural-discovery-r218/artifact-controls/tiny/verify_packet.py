"""Read-only exact-selection/mode verifier. Supply detached anchors explicitly.
No hashes are trusted from ANCHORS.json. The caller supplies the three anchors.
MANIFEST.json, REPORT.md, ANCHORS.json and artifact-controls/ are outside selection.
"""
import argparse, hashlib, json, os, stat
from pathlib import Path, PurePosixPath

def sha(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1048576),b''):h.update(b)
 return h.hexdigest()
def selection(root):
 files=[];dirs=[]
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  rel=Path(base).relative_to(root)
  ds[:]=[x for x in ds if not (rel==Path('.') and x=='artifact-controls')]
  for d in ds:
   p=Path(base)/d
   if p.is_symlink():raise ValueError('symlink directory')
   dirs.append(p.relative_to(root).as_posix())
  for n in fs:
   p=Path(base)/n;s=p.relative_to(root).as_posix()
   if s in {'MANIFEST.json','REPORT.md','ANCHORS.json'}:continue
   if p.is_symlink() or not p.is_file():raise ValueError('nonregular selection')
   files.append(s)
 return sorted(files),sorted(dirs)
def verify(root,manifest_sha,final_sha,report_sha):
 for n,h in [('MANIFEST.json',manifest_sha),('FINAL.md',final_sha),('REPORT.md',report_sha)]:
  if sha(root/n)!=h:raise ValueError('detached anchor mismatch: '+n)
 m=json.loads((root/'MANIFEST.json').read_bytes());fs,ds=selection(root)
 if fs!=sorted(m['files']):raise ValueError('exact file selection mismatch')
 if ds!=sorted(m['directories']):raise ValueError('exact directory selection mismatch')
 for n,e in m['files'].items():
  q=PurePosixPath(n)
  if q.is_absolute() or '..' in q.parts:raise ValueError('invalid relative path')
  p=root/n
  if p.stat().st_size!=e['bytes'] or sha(p)!=e['sha256']:raise ValueError('file bytes mismatch: '+n)
  if stat.S_IMODE(p.stat().st_mode)!=int(e['mode'],8):raise ValueError('file mode mismatch: '+n)
 for n,mode in m['directories'].items():
  if stat.S_IMODE((root/n).stat().st_mode)!=int(mode,8):raise ValueError('directory mode mismatch: '+n)
 return len(fs),len(ds)
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--manifest-sha',required=True);p.add_argument('--final-sha',required=True);p.add_argument('--report-sha',required=True);a=p.parse_args()
 n,d=verify(Path(a.root),a.manifest_sha,a.final_sha,a.report_sha)
 print(f'Exact selection, bytes and modes verified read-only: {n} files, {d} directories; all three supplied detached anchors match.')
