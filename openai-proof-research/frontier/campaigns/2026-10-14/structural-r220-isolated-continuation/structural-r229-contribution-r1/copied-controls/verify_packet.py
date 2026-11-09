"""Read-only exact-selection/mode verifier. Explicit detached anchors are mandatory.
Artifact checks only: this script makes no mathematical or contribution decision.
"""
from pathlib import Path, PurePosixPath
import argparse, hashlib, json, os, stat, sys
FORMAT='structural-r229-contribution-r1-selection-v1'
p=argparse.ArgumentParser()
for n in ['packet','manifest-sha256','final-sha256','report','report-sha256']:p.add_argument('--'+n,required=True)
a=p.parse_args();root=Path(a.packet);report=Path(a.report)
def need(ok,msg):
 if not ok:raise ValueError(msg)
def sha(path):return hashlib.sha256(path.read_bytes()).hexdigest()
def mode(path):return f'{stat.S_IMODE(path.lstat().st_mode):04o}'
try:
 need(root.is_dir() and not root.is_symlink(),'packet root type')
 for f,h in [(root/'MANIFEST.json',a.manifest_sha256),(root/'FINAL.md',a.final_sha256),(report,a.report_sha256)]:
  need(f.is_file() and not f.is_symlink(),'anchor target type')
  need(len(h)==64 and all(c in '0123456789abcdef' for c in h),'anchor format')
  need(sha(f)==h,'detached anchor mismatch: '+f.name)
 m=json.loads((root/'MANIFEST.json').read_bytes());need(m['format']==FORMAT,'selection format')
 need(mode(root)==m['root_mode']=='0500','packet root mode')
 need(mode(root/'MANIFEST.json')=='0400','manifest mode')
 entries=m['entries'];expected={}
 for e in entries:
  r=PurePosixPath(e['path'])
  need(not r.is_absolute() and '..' not in r.parts and r.as_posix()==e['path'] and e['path'] not in ['', '.', 'MANIFEST.json'],'unsafe member')
  need(e['path'] not in expected,'duplicate member');expected[e['path']]=e
 actual={}
 def visit(d):
  for item in os.scandir(d):
   f=Path(item.path);r=f.relative_to(root).as_posix()
   need(not item.is_symlink(),'symlink member')
   if r=='MANIFEST.json':continue
   need(r in expected,'extra selection member: '+r)
   actual[r]=f
   if item.is_dir(follow_symlinks=False):visit(f)
 visit(root);need(set(actual)==set(expected),'missing selection member')
 for r,e in expected.items():
  f=actual[r];need(mode(f)==e['mode'],'member mode mismatch: '+r)
  if e['type']=='directory':need(f.is_dir(),'directory type: '+r)
  else:
   need(e['type']=='file' and f.is_file(),'file type: '+r)
   need(f.stat().st_size==e['bytes'] and sha(f)==e['sha256'],'member bytes mismatch: '+r)
 print(json.dumps({'artifact_check':'exact selection, modes, bytes and explicit detached anchors agree','files':sum(e['type']=='file'for e in entries),'directories':sum(e['type']=='directory'for e in entries),'mathematical_gate':False}))
except Exception as ex:
 print('ARTIFACT REJECTION: '+str(ex),file=sys.stderr);sys.exit(1)
