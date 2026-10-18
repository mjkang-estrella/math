#!/usr/bin/env python3
"""Read-only exact-inventory verifier. Copyright Myeongjin Kang; MIT."""
import argparse,hashlib,json,os,pathlib,re,stat,sys

def check(root,anchor):
 if not re.fullmatch('[0-9a-f]{64}',anchor):raise ValueError('malformed external anchor')
 root=pathlib.Path(os.path.abspath(root))
 for p in [root,*root.parents]:
  s=p.lstat()
  if stat.S_ISLNK(s.st_mode) or not stat.S_ISDIR(s.st_mode):raise ValueError('root or ancestor not a real directory')
 manifest=root/'MANIFEST.json';ms=manifest.lstat()
 if not stat.S_ISREG(ms.st_mode) or ms.st_nlink!=1:raise ValueError('manifest not a singly linked regular file')
 raw=manifest.read_bytes()
 if hashlib.sha256(raw).hexdigest()!=anchor:raise ValueError('external manifest anchor mismatch')
 m=json.loads(raw)
 if m.get('format')!='rcs128-exact-inventory-v1':raise ValueError('unsupported manifest format')
 expected=m['files'];ed=m['directories']
 if len(ed)!=len(set(ed)) or '' in ed:raise ValueError('invalid directory list')
 for n in [*expected,*ed]:
  q=pathlib.PurePosixPath(n)
  if q.is_absolute() or '..' in q.parts or str(q)!=n or n=='MANIFEST.json':raise ValueError('invalid manifest path')
 actual={};dirs=[]
 def walk(d):
  for entry in os.scandir(d):
   p=pathlib.Path(entry.path);n=p.relative_to(root).as_posix();s=entry.stat(follow_symlinks=False)
   if stat.S_ISLNK(s.st_mode):raise ValueError('symlink: '+n)
   if stat.S_ISDIR(s.st_mode):dirs.append(n);walk(p)
   elif stat.S_ISREG(s.st_mode):
    if s.st_nlink!=1:raise ValueError('hardlink: '+n)
    if n!='MANIFEST.json':actual[n]={'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':s.st_size}
   else:raise ValueError('nonregular node: '+n)
 walk(root)
 if set(dirs)!=set(ed):raise ValueError('directory inventory mismatch')
 if set(actual)!=set(expected):raise ValueError('file inventory mismatch')
 for n,x in expected.items():
  if x!=actual[n]:raise ValueError('file content/size mismatch: '+n)
 return {'status':'PASS','manifest_sha256':anchor,'files':len(actual),'directories':len(dirs),'verification':'read-only; exact inventory and caller-supplied external anchor'}
if __name__=='__main__':
 p=argparse.ArgumentParser();p.add_argument('--root',type=pathlib.Path,default=pathlib.Path(__file__).absolute().parent);p.add_argument('--anchor',required=True);a=p.parse_args()
 try:print(json.dumps(check(a.root,a.anchor),sort_keys=True))
 except Exception as e:print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
