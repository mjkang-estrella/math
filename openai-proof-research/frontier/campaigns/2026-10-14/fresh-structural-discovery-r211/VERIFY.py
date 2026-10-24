"""Read-only exact-packet verifier. Supply all three detached anchors explicitly.
Only the supplied root's packet subtree and its named seal files are read.
No acquisition, source truth audit, mathematical grade, or file mutation occurs.
"""
from pathlib import Path, PurePosixPath
import argparse,hashlib,json,os,stat,sys

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for block in iter(lambda:f.read(1024*1024),b''):h.update(block)
 return h.hexdigest()

def verify(root,anchors):
 root=Path(root)
 for name,want in anchors.items():
  p=root/name
  if p.is_symlink() or not p.is_file():raise ValueError('missing or linked anchor: '+name)
  if digest(p)!=want:raise ValueError('detached anchor mismatch: '+name)
  if stat.S_IMODE(p.stat().st_mode)!=0o644:raise ValueError('anchor mode: '+name)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m.get('schema')!='r211-exact-packet-v1':raise ValueError('manifest schema')
 if digest(Path(__file__))!=m['verifier_sha256']:raise ValueError('verifier digest')
 expected={}
 for e in m['files']:
  p=PurePosixPath(e['path'])
  if p.is_absolute() or '..' in p.parts or not p.parts or p.parts[0]!='packet':raise ValueError('unsafe selection')
  if str(p) in expected:raise ValueError('duplicate selection')
  expected[str(p)]=e
 observed={};dirs={}
 def walk(p):
  if p.is_symlink() or not p.is_dir():raise ValueError('linked or missing packet directory')
  rel=p.relative_to(root).as_posix();dirs[rel]=stat.S_IMODE(p.stat().st_mode)
  for e in os.scandir(p):
   q=Path(e.path)
   if e.is_symlink():raise ValueError('linked packet entry')
   if e.is_dir(follow_symlinks=False):walk(q)
   elif e.is_file(follow_symlinks=False):observed[q.relative_to(root).as_posix()]=q
   else:raise ValueError('nonregular packet entry')
 walk(root/'packet')
 if set(observed)!=set(expected):raise ValueError('exact selection mismatch')
 if dirs!=m['directories']:raise ValueError('directory selection or modes')
 for name,p in observed.items():
  e=expected[name]
  if p.stat().st_size!=e['bytes'] or digest(p)!=e['sha256']:raise ValueError('file bytes: '+name)
  if stat.S_IMODE(p.stat().st_mode)!=e['mode']:raise ValueError('file mode: '+name)
 return {'artifact_only':True,'selected_files':len(expected),'selected_directories':len(dirs),'exact_selection':True,'hashes':True,'modes':True,'no_mathematical_verdict':True}

if __name__=='__main__':
 ap=argparse.ArgumentParser();ap.add_argument('--root',required=True)
 for x in ['final','manifest','report']:ap.add_argument('--'+x+'-sha256',required=True)
 a=ap.parse_args()
 try:
  out=verify(a.root,{'FINAL.md':a.final_sha256,'MANIFEST.json':a.manifest_sha256,'outside/REPORT.md':a.report_sha256})
  print(json.dumps(out,sort_keys=True))
 except Exception as e:
  print(json.dumps({'artifact_only':True,'error':str(e)}));sys.exit(1)
