"""Read-only exact-membership verifier. Anchors must come from outside the checked root."""
import sys,re,json,hashlib,os,stat
from pathlib import Path
ENV=('FINAL.md','MANIFEST.json','REPORT.md')
def sha(b):return hashlib.sha256(b).hexdigest()
def inventory(root):
 files={};dirs=[]
 def walk(p):
  for e in sorted(os.scandir(p),key=lambda e:e.name):
   q=Path(e.path);rel=q.relative_to(root).as_posix();st=e.stat(follow_symlinks=False)
   if stat.S_ISLNK(st.st_mode):raise ValueError('symlink: '+rel)
   if stat.S_ISDIR(st.st_mode):dirs.append(rel);walk(q)
   elif stat.S_ISREG(st.st_mode):
    if st.st_nlink!=1:raise ValueError('hardlink: '+rel)
    b=q.read_bytes();files[rel]={'bytes':len(b),'sha256':sha(b)}
   else:raise ValueError('nonregular: '+rel)
 walk(root);return files,sorted(dirs)
def main():
 if len(sys.argv)!=5:raise ValueError('usage: verify.py ROOT FINAL_SHA MANIFEST_SHA REPORT_SHA')
 root=Path(sys.argv[1]).absolute()
 if root.is_symlink() or not root.is_dir():raise ValueError('invalid root')
 anchors=sys.argv[2:]
 if not all(re.fullmatch('[0-9a-f]{64}',a) for a in anchors):raise ValueError('invalid anchor format')
 for n,a in zip(ENV,anchors):
  p=root/n; st=p.lstat()
  if not stat.S_ISREG(st.st_mode) or st.st_nlink!=1:raise ValueError('invalid envelope '+n)
  if sha(p.read_bytes())!=a:raise ValueError('detached anchor mismatch: '+n)
 m=json.loads((root/'MANIFEST.json').read_text())
 if m.get('format')!='r115-exact-v1' or m.get('outside_envelopes')!=list(ENV):raise ValueError('manifest schema')
 expected=m['files']; ds=m['directories']
 if not isinstance(expected,dict) or not isinstance(ds,list) or len(set(ds))!=len(ds):raise ValueError('membership schema')
 for n in list(expected)+ds:
  p=Path(n)
  if p.is_absolute() or '..' in p.parts or p.as_posix()!=n or n in ENV:raise ValueError('unsafe member')
 actual,dirs=inventory(root)
 if set(actual)!=set(expected)|set(ENV):raise ValueError('file membership mismatch')
 if dirs!=sorted(ds):raise ValueError('directory membership mismatch')
 for n,want in expected.items():
  if actual[n]!=want:raise ValueError('payload mismatch: '+n)
 print(json.dumps({'artifact_only':'exact identities and membership match','payload_files':len(expected),'outside_envelopes':3,'directories':len(dirs),'read_only':True}))
if __name__=='__main__':
 try:main()
 except Exception as e:print(type(e).__name__+': '+str(e),file=sys.stderr);sys.exit(1)
