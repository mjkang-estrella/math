#!/usr/bin/env python3
"""Read-only exact packet membership/byte verification. Not a mathematical gate."""
import argparse, hashlib, json, os, stat
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b): return hashlib.sha256(b).hexdigest()
def members(root):
 result=set()
 for base,dirs,files in os.walk(root,topdown=True,followlinks=False):
  for n in dirs:
   p=Path(base)/n
   if p.is_symlink(): raise ValueError('symlink directory: '+str(p))
  for n in files:
   p=Path(base)/n
   if p.is_symlink() or not stat.S_ISREG(p.stat().st_mode): raise ValueError('nonregular member: '+str(p))
   rel=p.relative_to(root).as_posix()
   if rel not in ENVELOPES: result.add(rel)
 return result

def verify(root,anchors):
 if not root.is_dir() or root.is_symlink(): raise ValueError('invalid root')
 for name,h in anchors.items():
  p=root/name
  if p.is_symlink() or not p.is_file(): raise ValueError('missing/nonregular envelope: '+name)
  if len(h)!=64 or sha(p.read_bytes())!=h: raise ValueError('detached anchor mismatch: '+name)
 doc=json.loads((root/'MANIFEST.json').read_bytes());entries=doc['files'];expected=set()
 for e in entries:
  n=e['path'];p=Path(n)
  if p.is_absolute() or '..' in p.parts or n in ENVELOPES or p.as_posix()!=n or n in expected: raise ValueError('invalid/duplicate payload path')
  expected.add(n)
 if members(root)!=expected: raise ValueError('payload membership mismatch')
 for e in entries:
  b=(root/e['path']).read_bytes()
  if len(b)!=e['size'] or sha(b)!=e['sha256']: raise ValueError('payload identity mismatch: '+e['path'])
 return {'verified_payload_files':len(entries),'outside_envelopes':3,'scope':'bytes and regular-file membership only'}
if __name__=='__main__':
 a=argparse.ArgumentParser(description=__doc__);a.add_argument('root',type=Path)
 a.add_argument('--final',required=True);a.add_argument('--manifest',required=True);a.add_argument('--report',required=True);v=a.parse_args()
 try:print(json.dumps(verify(v.root,{'FINAL.md':v.final,'MANIFEST.json':v.manifest,'REPORT.md':v.report}),sort_keys=True))
 except (ValueError,OSError,KeyError,TypeError,json.JSONDecodeError) as e:a.exit(1,str(e)+'\n')
