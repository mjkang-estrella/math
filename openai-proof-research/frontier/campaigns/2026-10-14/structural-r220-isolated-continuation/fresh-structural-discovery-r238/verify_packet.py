#!/usr/bin/env python3
"""Read-only exact-selection verification with explicit detached anchors."""
import argparse,hashlib,json,stat
from pathlib import Path,PurePosixPath

def sha(b):return hashlib.sha256(b).hexdigest()
def verify(root,manifest_sha,final_sha,report,report_sha):
 root=Path(root);report=Path(report)
 assert root.is_dir() and not root.is_symlink(), 'packet root'
 m=root/'MANIFEST.json';assert not m.is_symlink(), 'manifest symlink'
 mb=m.read_bytes();assert sha(mb)==manifest_sha,'manifest anchor'
 j=json.loads(mb);assert j['schema']=='structural238-exact-packet-v1','schema'
 assert stat.S_IMODE(m.stat().st_mode)==int(j['manifest_mode'],8),'manifest mode'
 expected={};dirs={}
 for e in j['files']:
  name=e['path'];p=PurePosixPath(name)
  assert not p.is_absolute() and '..' not in p.parts and name!='MANIFEST.json','unsafe path'
  assert name not in expected,'duplicate file';expected[name]=e
 for e in j['directories']:
  assert e['path'] not in dirs,'duplicate directory';dirs[e['path']]=e['mode']
 actual_files=set();actual_dirs={'.'}
 for p in root.rglob('*'):
  assert not p.is_symlink(),'symlink'
  rel=p.relative_to(root).as_posix()
  if p.is_dir():actual_dirs.add(rel)
  elif p.is_file():actual_files.add(rel)
  else:raise AssertionError('nonregular entry')
 assert actual_files==set(expected)|{'MANIFEST.json'},'exact file selection'
 assert actual_dirs==set(dirs),'exact directory selection'
 for name,mode in dirs.items():assert stat.S_IMODE((root/name).stat().st_mode)==int(mode,8),'directory mode'
 for name,e in expected.items():
  p=root/name;b=p.read_bytes()
  assert len(b)==e['bytes'],'file length'
  assert sha(b)==e['sha256'],'file hash'
  assert stat.S_IMODE(p.stat().st_mode)==int(e['mode'],8),'file mode'
 assert sha((root/'FINAL.md').read_bytes())==final_sha,'FINAL anchor'
 assert report.is_file() and not report.is_symlink(),'report file'
 assert sha(report.read_bytes())==report_sha,'outside REPORT anchor'
 return {'verified':True,'files':len(expected),'directories':len(dirs),'read_only':True}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--packet',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--final-sha256',required=True);p.add_argument('--report',required=True);p.add_argument('--report-sha256',required=True);a=p.parse_args()
 print(json.dumps(verify(a.packet,a.manifest_sha256,a.final_sha256,a.report,a.report_sha256),sort_keys=True))
