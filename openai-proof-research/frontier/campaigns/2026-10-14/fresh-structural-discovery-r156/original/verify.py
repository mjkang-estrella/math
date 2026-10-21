"""Read-only byte verifier. Three explicit independent envelope anchors are required."""
import argparse,hashlib,json,os,stat
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
 files={};dirs=['.']
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  ds.sort();fs.sort()
  for name in ds:
   p=Path(base)/name;s=p.lstat()
   if not stat.S_ISDIR(s.st_mode) or p.is_symlink():raise ValueError('non-directory '+str(p))
   dirs.append(p.relative_to(root).as_posix())
  for name in fs:
   p=Path(base)/name;s=p.lstat();rel=p.relative_to(root).as_posix()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('non-regular or linked file '+rel)
   files[rel]={'size':s.st_size,'sha256':digest(p)}
 return {'directories':sorted(dirs),'files':files}
def verify(root,anchors):
 got=inventory(root)
 for name,want in zip(['FINAL.md','MANIFEST.json','REPORT.md'],anchors):
  if len(want)!=64 or any(c not in '0123456789abcdef' for c in want):raise ValueError('invalid detached anchor')
  if got['files'].get(name,{}).get('sha256')!=want:raise ValueError('detached '+name+' mismatch')
 manifest=json.loads((root/'MANIFEST.json').read_text())
 payload={k:v for k,v in got['files'].items() if k not in ENVELOPES}
 if manifest!={'schema':1,'directories':got['directories'],'files':payload}:raise ValueError('exact payload/member mismatch')
 return {'verified_payload_files':len(payload),'verified_directories':len(got['directories']),'envelopes':3,'scope':'bytes and exact membership only; not mathematics; modes not bound'}
if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('root');ap.add_argument('final_sha256');ap.add_argument('manifest_sha256');ap.add_argument('report_sha256');a=ap.parse_args()
 try:print(json.dumps(verify(Path(a.root),[a.final_sha256,a.manifest_sha256,a.report_sha256]),sort_keys=True))
 except (ValueError,OSError,KeyError,TypeError) as e:ap.exit(1,'REJECT: '+str(e)+'\n')
