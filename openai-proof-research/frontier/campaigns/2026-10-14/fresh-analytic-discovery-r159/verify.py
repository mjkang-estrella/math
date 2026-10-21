"""Read-only byte/membership verification with three mandatory detached anchors."""
from pathlib import Path
import argparse,hashlib,json,os
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(b):return hashlib.sha256(b).hexdigest()
def verify(root,anchors):
 root=Path(root)
 for name,h in anchors.items():
  p=root/name
  if p.is_symlink() or digest(p.read_bytes())!=h:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes());expected={}
 for x in m['files']:
  p=Path(x['path'])
  if p.is_absolute() or '..' in p.parts or str(p) in ENVELOPES or str(p) in expected:raise ValueError('invalid membership')
  expected[str(p)]=x
 actual=set()
 for here,dirs,files in os.walk(root,followlinks=False):
  for name in dirs+files:
   if (Path(here)/name).is_symlink():raise ValueError('symlink encountered')
  for name in files:
   rel=str((Path(here)/name).relative_to(root))
   if rel not in ENVELOPES:actual.add(rel)
 if actual!=set(expected):raise ValueError('membership mismatch')
 for rel,x in expected.items():
  b=(root/rel).read_bytes()
  if len(b)!=x['bytes'] or digest(b)!=x['sha256']:raise ValueError('payload mismatch: '+rel)
 return {'artifact_check':'byte and membership verification succeeded','payload_files':len(expected)}
if __name__=='__main__':
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('--root',required=True)
 for n in ['final','manifest','report']:p.add_argument('--'+n,required=True)
 a=p.parse_args()
 try:print(json.dumps(verify(a.root,dict(zip(['FINAL.md','MANIFEST.json','REPORT.md'],[a.final,a.manifest,a.report])))))
 except (ValueError,OSError,KeyError) as e:print(json.dumps({'artifact_check':'rejected','reason':str(e)}));raise SystemExit(1)
