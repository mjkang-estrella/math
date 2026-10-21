#!/usr/bin/env python3
"""Read-only exact membership verifier. Supply three detached SHA256 anchors."""
import argparse,hashlib,json,os,stat
from pathlib import Path,PurePosixPath
ENVELOPES=('FINAL.md','MANIFEST.json','REPORT.md')
def digest(path):
 h=hashlib.sha256()
 with path.open('rb') as f:
  for block in iter(lambda:f.read(1048576),b''):h.update(block)
 return h.hexdigest()
def regular_files(root):
 result={}
 if root.is_symlink() or not root.is_dir():raise ValueError('root is not an ordinary directory')
 for base,ds,fs in os.walk(root,followlinks=False):
  for name in ds:
   p=Path(base)/name
   if p.is_symlink() or not p.is_dir():raise ValueError('unsafe directory: '+str(p))
  for name in fs:
   p=Path(base)/name;s=p.lstat()
   if not stat.S_ISREG(s.st_mode) or s.st_nlink!=1:raise ValueError('unsafe file: '+str(p))
   result[p.relative_to(root).as_posix()]=(p,s.st_size)
 return result
def verify(root,anchors):
 files=regular_files(root)
 for name,anchor in zip(ENVELOPES,anchors):
  if len(anchor)!=64 or any(c not in '0123456789abcdef' for c in anchor):raise ValueError('invalid detached anchor')
  if name not in files or digest(files[name][0])!=anchor:raise ValueError('detached anchor mismatch: '+name)
 obj=json.loads((root/'MANIFEST.json').read_text())
 if obj.get('schema')!='r149-exact-payload-v1' or obj.get('outside_envelopes')!=list(ENVELOPES):raise ValueError('wrong manifest schema')
 entries=obj['files'];expected={}
 for e in entries:
  name=e['path'];p=PurePosixPath(name)
  if p.is_absolute() or '..' in p.parts or p.as_posix()!=name or name in ENVELOPES or name in expected:raise ValueError('unsafe/duplicate manifest member')
  expected[name]=e
 actual=set(files)-set(ENVELOPES)
 if actual!=set(expected):raise ValueError('membership mismatch: missing='+str(sorted(set(expected)-actual))+' extra='+str(sorted(actual-set(expected))))
 for name,e in expected.items():
  p,size=files[name]
  if size!=e['size'] or digest(p)!=e['sha256']:raise ValueError('payload mismatch: '+name)
 return len(expected)
def main():
 p=argparse.ArgumentParser(description=__doc__);p.add_argument('root',type=Path)
 p.add_argument('--final-sha256',required=True);p.add_argument('--manifest-sha256',required=True);p.add_argument('--report-sha256',required=True)
 a=p.parse_args()
 try:n=verify(a.root,(a.final_sha256,a.manifest_sha256,a.report_sha256))
 except (ValueError,KeyError,OSError,TypeError,json.JSONDecodeError) as e:p.exit(1,'REJECT: '+str(e)+'\n')
 print('VERIFIED exact payload membership:',n,'files; three detached envelopes. Artifact bytes only.')
if __name__=='__main__':main()
