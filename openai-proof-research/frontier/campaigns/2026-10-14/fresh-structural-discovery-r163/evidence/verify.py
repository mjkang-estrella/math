#!/usr/bin/env python3
"""Read-only exact packet verifier. Three detached anchors are mandatory.
No imports of packet code, writes, repairs, subprocesses, or network operations.
Run with python -B. Artifact integrity is not a mathematical gate.
"""
import argparse,hashlib,json,os,re,stat,sys
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def verify(root,anchors):
 root=Path(root)
 if root.is_symlink() or not root.is_dir():raise ValueError('root must be a real directory')
 for name,want in anchors.items():
  if not re.fullmatch('[0-9a-f]{64}',want):raise ValueError('invalid detached anchor')
  p=root/name
  if p.is_symlink() or not p.is_file():raise ValueError('missing or symlink envelope: '+name)
  if stat.S_IMODE(p.stat().st_mode)!=0o444:raise ValueError('envelope mode: '+name)
  if digest(p)!=want:raise ValueError('detached anchor mismatch: '+name)
 m=json.loads((root/'MANIFEST.json').read_text())
 if set(m)!={'format','root_mode','files','directories'} or m['format']!='r163-exact-v1':raise ValueError('manifest schema')
 if stat.S_IMODE(root.stat().st_mode)!=m['root_mode']:raise ValueError('root mode')
 actual_files={};actual_dirs={}
 for base,dirs,files in os.walk(root,followlinks=False):
  for name in dirs+files:
   p=Path(base)/name;rel=p.relative_to(root).as_posix();s=p.lstat()
   if stat.S_ISLNK(s.st_mode):raise ValueError('symlink: '+rel)
   if stat.S_ISDIR(s.st_mode):actual_dirs[rel]=stat.S_IMODE(s.st_mode)
   elif stat.S_ISREG(s.st_mode):
    if rel not in ENVELOPES:actual_files[rel]={'bytes':s.st_size,'sha256':digest(p),'mode':stat.S_IMODE(s.st_mode)}
   else:raise ValueError('nonregular member: '+rel)
 if actual_dirs!=m['directories']:raise ValueError('directory membership/mode mismatch')
 if actual_files!=m['files']:raise ValueError('file membership/bytes/hash/mode mismatch')
 return len(actual_files),len(actual_dirs)
def main():
 a=argparse.ArgumentParser();a.add_argument('root');a.add_argument('--final-sha',required=True);a.add_argument('--manifest-sha',required=True);a.add_argument('--report-sha',required=True);p=a.parse_args()
 try:
  f,d=verify(p.root,{'FINAL.md':p.final_sha,'MANIFEST.json':p.manifest_sha,'REPORT.md':p.report_sha})
  print(f'INTEGRITY ONLY: {f} payload files, {d} directories; three detached envelopes match.')
 except Exception as e:
  print('REJECT: '+str(e),file=sys.stderr);return 1
 return 0
if __name__=='__main__':sys.exit(main())
