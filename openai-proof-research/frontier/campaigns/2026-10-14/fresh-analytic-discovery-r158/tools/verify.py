#!/usr/bin/env python3
"""Read-only membership/byte verification. Supply independent envelope anchors."""
from pathlib import Path
import argparse,hashlib,json,os
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def inventory(root):
 out={}
 for directory,dirs,files in os.walk(root,followlinks=False):
  d=Path(directory)
  for name in dirs:
   if (d/name).is_symlink():raise ValueError('symlink directory')
  for name in files:
   p=d/name
   if p.is_symlink() or not p.is_file():raise ValueError('nonregular payload')
   rel=p.relative_to(root).as_posix()
   if rel not in ENVELOPES:out[rel]={'size':p.stat().st_size,'sha256':digest(p)}
 return dict(sorted(out.items()))
def verify(root,anchors):
 root=Path(root)
 if set(anchors)!=ENVELOPES:raise ValueError('three detached anchors required')
 for name,sha in anchors.items():
  if len(sha)!=64 or digest(root/name)!=sha:raise ValueError('envelope anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m.get('schema')!='r158-byte-membership-v1' or m.get('excluded')!=sorted(ENVELOPES):raise ValueError('manifest schema/exclusions')
 if inventory(root)!=m['files']:raise ValueError('payload membership or bytes mismatch')
 return len(m['files'])
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('root');a.add_argument('--final',required=True);a.add_argument('--manifest',required=True);a.add_argument('--report',required=True);o=a.parse_args()
 n=verify(o.root,{'FINAL.md':o.final,'MANIFEST.json':o.manifest,'REPORT.md':o.report});print(f'Artifact membership/bytes match: {n} payloads + 3 envelopes. No mathematical gate.')
