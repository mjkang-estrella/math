"""Read-only integrity verifier. Explicit detached anchors are mandatory.
No network, subprocess, repair, writes, or mathematical tests.
Run with python -B to suppress interpreter bytecode side effects.
"""
import argparse,hashlib,json,os,re
from pathlib import Path
ENVELOPES={'MANIFEST.json','REPORT.md','FINAL.json'}
FORBIDDEN=re.compile(r'structural.*r144|arithmetic.*r10[89]|t185r144',re.I)
def digest(b): return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={};dirs=[]
 for base, subdirs, names in os.walk(root,topdown=True,followlinks=False):
  for name in sorted(subdirs):
   p=Path(base)/name
   if p.is_symlink(): raise ValueError('symlink directory')
   if FORBIDDEN.search(name): raise ValueError('isolated component; not descended')
   dirs.append(p.relative_to(root).as_posix())
  subdirs.sort()
  for name in sorted(names):
   p=Path(base)/name; rel=p.relative_to(root).as_posix()
   if FORBIDDEN.search(name): raise ValueError('isolated filename; not read')
   if p.is_symlink() or not p.is_file(): raise ValueError('nonregular payload')
   if rel in ENVELOPES: continue
   b=p.read_bytes();files[rel]={'size':len(b),'sha256':digest(b)}
 return dict(sorted(files.items())),sorted(dirs)
def verify(root,anchors):
 root=Path(root)
 if root.is_symlink() or not root.is_dir(): raise ValueError('root must be an ordinary directory')
 for n in sorted(ENVELOPES):
  if not re.fullmatch('[0-9a-f]{64}',anchors.get(n,'')): raise ValueError('explicit detached anchor required')
  p=root/n
  if p.is_symlink() or not p.is_file(): raise ValueError('missing/nonregular envelope')
  if digest(p.read_bytes())!=anchors[n]: raise ValueError('detached anchor mismatch: '+n)
 m=json.loads((root/'MANIFEST.json').read_text());f=json.loads((root/'FINAL.json').read_text())
 if m.get('schema')!=1: raise ValueError('unknown schema')
 if f.get('manifest_sha256')!=anchors['MANIFEST.json'] or f.get('report_sha256')!=anchors['REPORT.md']:
  raise ValueError('final envelope binding mismatch')
 files,dirs=inventory(root)
 if m.get('files')!=files or m.get('directories')!=dirs: raise ValueError('exact payload inventory mismatch')
 return {'integrity':'verified','payload_files':len(files),'payload_directories':len(dirs),'mathematical_gate':False}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--root',default=str(Path(__file__).resolve().parent))
 p.add_argument('--manifest-sha256',required=True)
 p.add_argument('--report-sha256',required=True)
 p.add_argument('--final-sha256',required=True)
 a=p.parse_args()
 try:
  print(json.dumps(verify(a.root,{'MANIFEST.json':a.manifest_sha256,'REPORT.md':a.report_sha256,'FINAL.json':a.final_sha256}),sort_keys=True))
 except (ValueError,OSError,KeyError,json.JSONDecodeError) as e:
  p.exit(1,'Integrity verification rejected: '+str(e)+'\n')
