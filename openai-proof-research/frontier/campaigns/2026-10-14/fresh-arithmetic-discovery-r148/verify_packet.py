#!/usr/bin/env python3
"""Read-only byte/mode verification; never a mathematical gate. No traversal."""
import argparse, hashlib, json, stat
from pathlib import Path, PurePosixPath

def digest(b): return hashlib.sha256(b).hexdigest()
def safe(root,name):
 p=PurePosixPath(name)
 if p.is_absolute() or '..' in p.parts: raise ValueError('unsafe packet path')
 q=root.joinpath(*p.parts)
 if q.is_symlink() or not q.is_file(): raise ValueError('not a regular payload: '+name)
 return q

def verify(root,anchors,project=None):
 for name,anchor in zip(['FINAL.md','MANIFEST.json','REPORT.md'],anchors):
  if len(anchor)!=64 or digest(safe(root,name).read_bytes())!=anchor:
   raise ValueError('detached anchor mismatch: '+name)
 manifest=json.loads((root/'MANIFEST.json').read_text())
 seen=set()
 for row in manifest['files']:
  name=row['path']
  if name in seen:raise ValueError('duplicate payload')
  seen.add(name);p=safe(root,name);b=p.read_bytes()
  if len(b)!=row['bytes'] or digest(b)!=row['sha256']:raise ValueError('payload mismatch: '+name)
  if stat.S_IMODE(p.stat().st_mode)!=row['mode']:raise ValueError('mode mismatch: '+name)
 if project is not None:
  bindings=json.loads(safe(root,'private/source-bindings.json').read_text())
  for row in bindings:
   b=safe(root,row['path']).read_bytes()
   blob=hashlib.sha1(b'blob '+str(len(b)).encode()+b'\0'+b).hexdigest()
   if blob!=row['git_blob']:raise ValueError('canonical blob mismatch')
  tree=safe(project,'sources/preprints-tree.json').read_bytes()
  if len(tree)!=4858136 or digest(tree)!='eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b':raise ValueError('tree mismatch')
  j=json.loads(tree)
  if j.get('truncated') or len(j['tree'])!=13223:raise ValueError('tree incomplete')
  entries={(e['path'] if e['path'].startswith('preprints/') else 'preprints/'+e['path']):e for e in j['tree']}
  for row in bindings:
   e=entries[row['upstream_path']]
   if e['sha']!=row['git_blob'] or e['size']!=row['bytes']:raise ValueError('tree binding mismatch')
  originals=json.loads(safe(root,'private/original-anchors.json').read_text())
  for row in originals:
   p=safe(project,row['path'])
   with p.open('rb') as f:f.seek(row['start']);b=f.read(row['end']-row['start'])
   if len(b)!=row['end']-row['start'] or digest(b)!=row['sha256']:raise ValueError('original range mismatch: '+row['path'])
  print('Pinned source bindings and exact original ranges match.')
 print('Selected payload bytes/modes and all three explicit detached anchors match:',len(seen),'payloads.')
 print('No mathematical grade or exhaustive-directory claim is implied.')

if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',type=Path,required=True)
 p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
 p.add_argument('--project',type=Path)
 a=p.parse_args();verify(a.root,[a.final_sha256,a.manifest_sha256,a.report_sha256],a.project)
