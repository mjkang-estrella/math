#!/usr/bin/env python3
"""Read-only byte/membership verifier. Mathematical validity is outside its scope."""
from pathlib import Path
import argparse,hashlib,json,os,stat,sys
ENV={'FINAL.md','MANIFEST.json','REPORT.md'}
def sha(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={};dirs={'.':stat.S_IMODE(root.stat().st_mode)}
 for here,ds,fs in os.walk(root,topdown=True,followlinks=False):
  for n in ds:
   p=Path(here)/n
   if p.is_symlink():raise ValueError('directory symlink: '+str(p))
   dirs[p.relative_to(root).as_posix()]=stat.S_IMODE(p.stat().st_mode)
  for n in fs:
   p=Path(here)/n;rel=p.relative_to(root).as_posix()
   if p.is_symlink() or not p.is_file():raise ValueError('nonregular member: '+rel)
   if rel in ENV:continue
   b=p.read_bytes();files[rel]={'bytes':len(b),'sha256':sha(b),'mode':stat.S_IMODE(p.stat().st_mode)}
 return files,dirs
def verify(root,anchors):
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
 for name,digest in anchors.items():
  p=root/name
  if p.is_symlink() or not p.is_file():raise ValueError('missing/nonregular envelope '+name)
  if len(digest)!=64 or sha(p.read_bytes())!=digest:raise ValueError('detached anchor mismatch '+name)
 m=json.loads((root/'MANIFEST.json').read_bytes())
 if m['schema']!='r164-exact-selection-v1':raise ValueError('schema')
 actual,dirs=inventory(root)
 if actual!=m['files']:raise ValueError('payload bytes, modes, or exact membership mismatch')
 if dirs!=m['directories']:raise ValueError('directory modes or exact membership mismatch')
 for n,mode in m['envelope_modes'].items():
  if stat.S_IMODE((root/n).stat().st_mode)!=mode:raise ValueError('envelope mode mismatch '+n)
 if 'tools/verify_packet.py' not in actual:raise ValueError('verifier missing from payload')
 if actual['tools/verify_packet.py']['sha256']!=sha(Path(__file__).read_bytes()):raise ValueError('executing verifier differs from sealed copy')
 return {'payload_files':len(actual),'directories_including_root':len(dirs),'outside_envelopes':3,'result':'byte/membership checks only; no mathematical gate'}
if __name__=='__main__':
 a=argparse.ArgumentParser();a.add_argument('--root',required=True);a.add_argument('--final-sha256',required=True);a.add_argument('--manifest-sha256',required=True);a.add_argument('--report-sha256',required=True);x=a.parse_args()
 try:
  out=verify(Path(x.root),{'FINAL.md':x.final_sha256,'MANIFEST.json':x.manifest_sha256,'REPORT.md':x.report_sha256});print(json.dumps(out))
 except Exception as ex:print('FAIL: '+str(ex),file=sys.stderr);sys.exit(1)
