"""Read-only exact review-packet integrity checks, never a mathematical gate.
No writes, subprocesses, network, repair, source execution or recursive verifier calls.
Use python -B. All three detached anchors are required.
"""
from pathlib import Path
import argparse,hashlib,json,os,re
ENVELOPES={'REPORT.md','FINAL.json','MANIFEST.json'}
def digest(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={};dirs=[]
 for base,ds,ns in os.walk(root,topdown=True,followlinks=False):
  ds.sort()
  for d in ds:
   p=Path(base)/d
   if p.is_symlink():raise ValueError('symlink directory')
   dirs.append(p.relative_to(root).as_posix())
  for n in sorted(ns):
   p=Path(base)/n;r=p.relative_to(root).as_posix()
   if p.is_symlink() or not p.is_file():raise ValueError('nonregular file')
   if r in ENVELOPES:continue
   b=p.read_bytes();files[r]={'size':len(b),'sha256':digest(b)}
 return dict(sorted(files.items())),sorted(dirs)
def verify(root,anchors):
 root=Path(root)
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 for n in sorted(ENVELOPES):
  h=anchors.get(n,'')
  if not re.fullmatch('[0-9a-f]{64}',h):raise ValueError('missing detached anchor')
  p=root/n
  if p.is_symlink() or not p.is_file():raise ValueError('missing/nonregular envelope')
  if digest(p.read_bytes())!=h:raise ValueError('detached mismatch: '+n)
 m=json.loads((root/'MANIFEST.json').read_text());f=json.loads((root/'FINAL.json').read_text())
 if m.get('schema')!=1:raise ValueError('schema')
 if f.get('manifest_sha256')!=anchors['MANIFEST.json'] or f.get('report_sha256')!=anchors['REPORT.md']:raise ValueError('envelope binding')
 files,dirs=inventory(root)
 if m.get('files')!=files or m.get('directories')!=dirs:raise ValueError('exact inventory mismatch')
 return {'artifact_integrity':'VERIFIED','payload_files':len(files),'directories':len(dirs),'mathematical_gate':False}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',default=str(Path(__file__).resolve().parent))
 for n in ['manifest','report','final']:p.add_argument('--'+n+'-sha256',required=True)
 a=p.parse_args()
 try: print(json.dumps(verify(a.root,{'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256,'FINAL.json':a.final_sha256}),sort_keys=True))
 except (OSError,ValueError,KeyError) as e:p.exit(1,'REJECTED: '+str(e)+'\n')
