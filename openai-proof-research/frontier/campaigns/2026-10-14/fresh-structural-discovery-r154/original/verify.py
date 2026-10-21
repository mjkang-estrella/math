"""Read-only byte/membership verifier. Independent detached anchors required.
No mathematical correctness, contribution, provenance-completeness or mode claim.
"""
import argparse,hashlib,json,os,stat,sys
from pathlib import Path
ENVELOPES={'FINAL.md','MANIFEST.json','REPORT.md'}
def digest(b): return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={};dirs=['.']
 for base,ds,fs in os.walk(root,topdown=True,followlinks=False):
  ds.sort();fs.sort()
  for name in ds:
   p=Path(base)/name;s=p.lstat()
   if not stat.S_ISDIR(s.st_mode) or p.is_symlink(): raise ValueError('non-directory or symlink: '+str(p))
   dirs.append(p.relative_to(root).as_posix())
  for name in fs:
   p=Path(base)/name;s=p.lstat(); rel=p.relative_to(root).as_posix()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1: raise ValueError('nonregular, symlink or hardlink: '+rel)
   if rel not in ENVELOPES:
    b=p.read_bytes();files[rel]={'size':len(b),'sha256':digest(b)}
 return {'files':files,'directories':sorted(dirs)}
def main():
 a=argparse.ArgumentParser();a.add_argument('root');a.add_argument('--final',required=True);a.add_argument('--manifest',required=True);a.add_argument('--report',required=True);o=a.parse_args();r=Path(o.root)
 if r.is_symlink() or not r.is_dir(): raise ValueError('invalid root')
 for name,want in [('FINAL.md',o.final),('MANIFEST.json',o.manifest),('REPORT.md',o.report)]:
  p=r/name;s=p.lstat()
  if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1: raise ValueError('invalid envelope '+name)
  if len(want)!=64 or digest(p.read_bytes())!=want: raise ValueError('detached anchor mismatch '+name)
 expected=json.loads((r/'MANIFEST.json').read_text()); actual=inventory(r)
 if expected!=actual: raise ValueError('exact file/directory inventory mismatch')
 print(json.dumps({'artifact_integrity':'matched','payload_files':len(actual['files']),'directories':len(actual['directories']),'outside_envelopes':3,'mathematical_gate':False}))
if __name__=='__main__':
 try: main()
 except (OSError,ValueError,KeyError) as e: print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
