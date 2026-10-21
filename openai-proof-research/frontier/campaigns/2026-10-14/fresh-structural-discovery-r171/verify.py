#!/usr/bin/env python3
"""Read-only byte/mode verifier. Explicit external anchors required; not a math gate."""
from pathlib import Path,PurePosixPath
import argparse,hashlib,json,stat
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def inspect(root,anchors):
 root=Path(root).resolve()
 for name,anchor in anchors.items():
  assert len(anchor)==64 and all(c in '0123456789abcdef' for c in anchor),'invalid anchor'
  p=root/name;assert not p.is_symlink(),'symlink envelope';assert sha(p.read_bytes())==anchor,'envelope mismatch: '+name
 m=json.loads((root/'MANIFEST.json').read_text());assert m['format']=='r171-exact-payload-v1'
 actual={};dirs={'.':stat.S_IMODE(root.stat().st_mode)}
 for p in root.rglob('*'):
  assert not p.is_symlink(),'symlink: '+str(p)
  rel=p.relative_to(root).as_posix()
  if p.is_dir():dirs[rel]=stat.S_IMODE(p.stat().st_mode)
  elif p.is_file() and rel not in ENVELOPES:
   b=p.read_bytes();actual[rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(p.stat().st_mode)}
  elif not p.is_file():raise AssertionError('nonregular object: '+rel)
 for rel in m['files']:
  q=PurePosixPath(rel);assert not q.is_absolute() and '..' not in q.parts,'unsafe manifest path'
 assert actual==m['files'],'payload membership/bytes/hash/mode mismatch'
 assert dirs==m['directories'],'directory membership/mode mismatch'
 return {'payload_files':len(actual),'directories':len(dirs),'artifact_check':'matches explicit anchors; no mathematical grade'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',required=True);p.add_argument('--final',required=True);p.add_argument('--manifest',required=True);p.add_argument('--report',required=True);a=p.parse_args()
 print(json.dumps(inspect(a.root,{'FINAL.md':a.final,'MANIFEST.json':a.manifest,'REPORT.md':a.report}),sort_keys=True))
