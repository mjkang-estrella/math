#!/usr/bin/env python3
"""Read-only exact-packet verifier. All three detached anchors are mandatory."""
import argparse,hashlib,json,re
from pathlib import Path,PurePosixPath

def digest(p):
 h=hashlib.sha256()
 with p.open('rb') as f:
  for b in iter(lambda:f.read(1<<20),b''):h.update(b)
 return h.hexdigest()
def main():
 a=argparse.ArgumentParser();a.add_argument('--root',required=True,type=Path)
 for k in ['final','manifest','report']:a.add_argument('--'+k,required=True)
 z=a.parse_args();r=z.root.resolve()
 for k,name in [('final','FINAL.md'),('manifest','MANIFEST.json'),('report','REPORT.md')]:
  expected=getattr(z,k)
  if not re.fullmatch('[0-9a-f]{64}',expected):raise ValueError('invalid explicit anchor: '+k)
  p=r/name
  if p.is_symlink() or digest(p)!=expected:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((r/'MANIFEST.json').read_text());assert m['schema']=='r162aj-exact-packet-v1'
 v=m['verifier'];assert v['path']=='verify.py'
 if (r/'verify.py').is_symlink() or digest(r/'verify.py')!=v['sha256']:raise ValueError('verifier mismatch')
 expected=set()
 for e in m['files']:
  s=e['path'];p=PurePosixPath(s)
  if p.is_absolute() or '..' in p.parts or not s.startswith('packet/') or s in expected:raise ValueError('invalid manifest path')
  expected.add(s);f=r/s
  if f.is_symlink() or not f.is_file() or f.stat().st_size!=e['bytes'] or digest(f)!=e['sha256']:raise ValueError('packet mismatch: '+s)
 actual=set()
 for p in (r/'packet').rglob('*'):
  if p.is_symlink():raise ValueError('symlink in packet')
  if p.is_file():actual.add(p.relative_to(r).as_posix())
 if actual!=expected:raise ValueError('packet inventory mismatch')
 print(json.dumps({'verified':True,'files':len(expected),'read_only':True,'mathematical_gate':False}))
if __name__=='__main__':main()
