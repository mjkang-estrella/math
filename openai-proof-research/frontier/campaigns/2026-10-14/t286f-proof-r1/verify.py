#!/usr/bin/env python3
"""MIT. Externally anchored exact-inventory verifier for the T286F proof-r1 review directory.
Usage: verify.py EXTERNAL_MANIFEST_SHA256 [AUTHOR_PACKET_DIR]
The SHA256 of this directory's manifest.json must come from the parent's external record.
Optionally also checks the author packet's manifest and named files against fixed dispatch hashes
(read-only). Never writes, never reseals, certifies bytes only, not mathematics.
"""
import hashlib,json,os,stat,sys
from pathlib import Path

AUTHOR={'manifest.json':'4d14a7c7515c455d2108f4dfc9cd64adf09539d31d57ff2bb71fb47418040af9',
 'candidate286f.md':'1b43b798570761b052fec9e017be89f519afd061c30217fd750543aac0265c2b',
 'scope286f.md':'f905fbf989c11ffe40ac99f9c89d9ccd36d546f77a1238e30f85ec7769c09398',
 'verify.py':'a2ecf261a60b59d3f4fccf72136abe30f5bc2c0f80a600b2120f16ec3e6fddca',
 'source-and-credit286f.md':'de08204c91883b694f61509de23edb2d3c8480cb3abaaf3b429a998697b1ddbc'}
def sha(b):return hashlib.sha256(b).hexdigest()
def nolinks(p):
 for q in (p,*p.parents):
  if not stat.S_ISDIR(q.lstat().st_mode):raise ValueError('non-directory or symlink ancestor')
def check(expected,author=None):
 script=Path(sys.argv[0])
 if '..' in script.parts:raise ValueError('parent traversal in invocation')
 if not script.is_absolute():script=Path.cwd()/script
 root=script.parent;nolinks(root)
 files={};dirs=[]
 def walk(p):
  for e in os.scandir(p):
   q=Path(e.path);rel=q.relative_to(root).as_posix();s=q.lstat()
   if stat.S_ISDIR(s.st_mode):dirs.append(rel);walk(q)
   elif stat.S_ISREG(s.st_mode):
    if s.st_nlink!=1:raise ValueError('hardlink: '+rel)
    if q.name=='manifest.json' and rel!='manifest.json':raise ValueError('nested manifest')
    files[rel]={'bytes':s.st_size,'sha256':sha(q.read_bytes())}
   else:raise ValueError('nonregular entry: '+rel)
 walk(root)
 if 'manifest.json' not in files:raise ValueError('missing manifest')
 raw=(root/'manifest.json').read_bytes()
 if sha(raw)!=expected:raise ValueError('external manifest anchor mismatch')
 m=json.loads(raw)
 if sorted(dirs)!=m['directories']:raise ValueError('directory inventory mismatch')
 del files['manifest.json']
 if files!=m['files']:raise ValueError('file inventory mismatch')
 out={'status':'PASS_REVIEW_INVENTORY','files':len(files),'directories':len(dirs),'verdict':m['verdict']}
 if author is not None:
  a=Path(author)
  if not a.is_absolute() or '..' in a.parts:raise ValueError('author packet path must be absolute')
  nolinks(a)
  for n,h in AUTHOR.items():
   q=a/n
   if not stat.S_ISREG(q.lstat().st_mode) or sha(q.read_bytes())!=h:raise ValueError('author packet mismatch: '+n)
  out['author_packet']='PASS_DISPATCH_HASHES'
 print(json.dumps(out))
if __name__=='__main__':
 try:
  if len(sys.argv) not in (2,3) or len(sys.argv[1])!=64 or any(c not in '0123456789abcdef' for c in sys.argv[1]):raise ValueError('external SHA256 argument required')
  check(sys.argv[1],sys.argv[2] if len(sys.argv)==3 else None)
 except Exception as e:print('FAIL: '+str(e),file=sys.stderr);sys.exit(1)
