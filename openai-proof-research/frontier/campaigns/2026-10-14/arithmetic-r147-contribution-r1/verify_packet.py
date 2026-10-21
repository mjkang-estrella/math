#!/usr/bin/env python3
"""Read-only explicit-anchor selected-packet verification; no mathematical grading."""
import argparse,hashlib,json,re,stat,sys
from pathlib import Path,PurePosixPath

def sha(b):return hashlib.sha256(b).hexdigest()
def safe(root,rel):
 p=PurePosixPath(rel)
 if p.is_absolute() or '..' in p.parts or not p.parts or p.as_posix()!=rel:raise ValueError('unsafe relative path')
 out=root
 for part in p.parts:
  out=out/part
  if out.is_symlink():raise ValueError('symlink not admitted: '+rel)
 return out

def main():
 p=argparse.ArgumentParser(description=__doc__)
 p.add_argument('--root',required=True)
 for n in ['final','manifest','report']:p.add_argument('--'+n+'-sha256',required=True)
 p.add_argument('--originals-project')
 a=p.parse_args();root=Path(a.root)
 for n in ['final','manifest','report']:
  expected=getattr(a,n+'_sha256')
  if not re.fullmatch('[0-9a-f]{64}',expected):raise ValueError('invalid explicit anchor')
  if sha(safe(root,n.upper()+'.'+('json' if n=='manifest' else 'md')).read_bytes())!=expected:raise ValueError(n+' detached anchor mismatch')
 m=json.loads(safe(root,'MANIFEST.json').read_text());seen=set()
 for x in m['files']:
  rel=x['path']
  if rel in seen or rel in ['FINAL.md','MANIFEST.json','REPORT.md','ANCHORS.json']:raise ValueError('duplicate or envelope payload')
  seen.add(rel);f=safe(root,rel);b=f.read_bytes()
  if len(b)!=x['bytes'] or sha(b)!=x['sha256']:raise ValueError('payload mismatch: '+rel)
  if 'mode' in x and stat.S_IMODE(f.stat().st_mode)!=x['mode']:raise ValueError('mode mismatch: '+rel)
 if 'frozen' in m:
  for x in m['frozen']:
   b=safe(root,x['path']).read_bytes()
   if len(b)!=x['bytes'] or sha(b)!=x['sha256']:raise ValueError('frozen binding mismatch')
 if 'source_authentication' in m:
  sa=json.loads(safe(root,m['source_authentication']).read_text())
  for x in sa['sources']:
   b=safe(root,'private/source/'+PurePosixPath(x['path']).name).read_bytes()
   if len(b)!=x['bytes'] or sha(b)!=x['sha256'] or hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()!=x['blob']:raise ValueError('source blob mismatch')
 checked=0
 if a.originals_project:
  project=Path(a.originals_project)
  for x in json.loads(safe(root,m['original_anchors']).read_text()):
   f=safe(project,x['path'])
   with f.open('rb') as s:s.seek(x['start']);b=s.read(x['end']-x['start'])
   if len(b)!=x['end']-x['start'] or sha(b)!=x['sha256']:raise ValueError('original slice mismatch: '+x['path'])
   if stat.S_IMODE(f.stat().st_mode)!=x['mode']:raise ValueError('original mode mismatch')
   checked+=1
  for x in json.loads(safe(root,m['immutable_inputs']).read_text()):
   f=safe(project,x['path']);b=f.read_bytes()
   if len(b)!=x['bytes'] or sha(b)!=x['sha256'] or stat.S_IMODE(f.stat().st_mode)!=x['mode']:raise ValueError('admitted input changed: '+x['path'])
   checked+=1
 print(json.dumps({'artifact_check':'OK','selected_files':len(seen),'explicit_original_checks':checked,'mathematical_grade':False}))

if __name__=='__main__':
 try:main()
 except (ValueError,OSError,KeyError,TypeError) as e:
  print('ARTIFACT CHECK FAILED: '+str(e),file=sys.stderr);sys.exit(1)
