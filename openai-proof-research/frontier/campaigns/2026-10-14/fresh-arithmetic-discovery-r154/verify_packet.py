#!/usr/bin/env python3
"""Read-only exact-packet verification. Explicit external anchors are required."""
import argparse,hashlib,json
from pathlib import Path,PurePosixPath

def digest(data):return hashlib.sha256(data).hexdigest()

def verify(root,final_sha,manifest_sha,report_sha):
 root=Path(root)
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
 anchors={'FINAL.md':final_sha,'MANIFEST.json':manifest_sha,'REPORT.md':report_sha}
 for name,want in anchors.items():
  if len(want)!=64 or any(c not in '0123456789abcdef' for c in want):raise ValueError('bad explicit anchor')
  p=root/name
  if p.is_symlink() or not p.is_file() or digest(p.read_bytes())!=want:raise ValueError('anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes())
 if m.get('schema')!='r154-exact-packet-v1':raise ValueError('wrong schema')
 seen=set()
 for a in m['files']:
  rel=a['path'];q=PurePosixPath(rel)
  if q.is_absolute() or '..' in q.parts or '.' in q.parts or str(q)!=rel or rel in seen:raise ValueError('unsafe or duplicate entry')
  seen.add(rel);p=root.joinpath(*q.parts)
  for parent in [p,*list(p.parents)[:len(q.parts)-1]]:
   if parent.is_symlink():raise ValueError('symlink entry')
  b=p.read_bytes()
  if len(b)!=a['bytes'] or digest(b)!=a['sha256']:raise ValueError('payload mismatch: '+rel)
 if 'FINAL.md' not in seen:raise ValueError('FINAL not bound by manifest')
 outside={'MANIFEST.json','REPORT.md','ANCHORS.json'}
 if seen & outside:raise ValueError('circular/outside entry')
 actual=set()
 for p in root.rglob('*'):
  if p.is_symlink():raise ValueError('symlink in packet')
  if p.is_file():actual.add(p.relative_to(root).as_posix())
 if actual!=seen|outside:raise ValueError('missing or unexpected files')
 if json.loads((root/'ANCHORS.json').read_bytes())!=anchors:raise ValueError('transport anchors disagree with explicit anchors')
 return {'files':len(seen),'payload_bytes':sum(a['bytes'] for a in m['files']),'artifact_integrity':'matched explicit anchors','mathematical_verdict':None}

if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--root',required=True);p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
 a=p.parse_args()
 try:print(json.dumps(verify(a.root,a.final_sha256,a.manifest_sha256,a.report_sha256),sort_keys=True))
 except (ValueError,OSError,KeyError,TypeError,json.JSONDecodeError) as e:p.exit(1,str(e)+'\n')
