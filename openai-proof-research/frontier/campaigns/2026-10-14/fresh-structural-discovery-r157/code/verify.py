#!/usr/bin/env python3
"""Read-only verifier. Supply ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256.
Detached anchors must come from the independent handoff, not this packet.
Checks exact file/directory membership, bytes, regular files and single links.
Does not authenticate modes. Never fetches, runs diagnostics, writes, or repairs.
"""
from pathlib import Path
import sys,json,hashlib,stat
ENVELOPES=('FINAL.md','MANIFEST.json','REPORT.md')
def sha(b):return hashlib.sha256(b).hexdigest()
def inspect(root):
 if root.is_symlink() or not root.is_dir():raise ValueError('bad root')
 files={};dirs=['.']
 def walk(p):
  for q in sorted(p.iterdir()):
   rel=q.relative_to(root).as_posix();s=q.lstat()
   if stat.S_ISLNK(s.st_mode):raise ValueError('symlink '+rel)
   if stat.S_ISDIR(s.st_mode):dirs.append(rel);walk(q)
   elif stat.S_ISREG(s.st_mode) and s.st_nlink==1:files[rel]={'size':s.st_size,'sha256':sha(q.read_bytes())}
   else:raise ValueError('nonregular or multilink '+rel)
 walk(root);return files,sorted(dirs)
def verify(root,anchors):
 files,dirs=inspect(root)
 for e,h in zip(ENVELOPES,anchors):
  if len(h)!=64 or files.get(e,{}).get('sha256')!=h:raise ValueError('detached anchor '+e)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m['schema']!='r157-exact-v1' or m['envelopes']!=list(ENVELOPES):raise ValueError('schema/envelopes')
 if dirs!=m['directories']:raise ValueError('directory membership')
 payload={k:v for k,v in files.items() if k not in ENVELOPES}
 if payload!=m['files']:raise ValueError('payload membership/bytes')
 return {'artifact_match':True,'payload_files':len(payload),'total_files':len(files),'directories_including_root':len(dirs),'mathematical_grade':None}
if __name__=='__main__':
 try:
  if len(sys.argv)!=5:raise ValueError('Usage: verify.py ROOT FINAL_SHA256 MANIFEST_SHA256 REPORT_SHA256')
  print(json.dumps(verify(Path(sys.argv[1]),sys.argv[2:])))
 except Exception as e:print(json.dumps({'artifact_match':False,'error':str(e)}));sys.exit(1)
