#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License.
"""Read-only artifact verification using mandatory external detached anchors.
Does not execute payload code, compile, download, or write caches/reports.
Does not certify mathematics, formal coverage, rights, novelty, or acceptance.
"""
import argparse,hashlib,json,stat,sys
from pathlib import Path,PurePosixPath
sys.dont_write_bytecode=True

def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def require(ok,msg):
 if not ok:raise ValueError(msg)
def regular(p):
 s=p.lstat();require(stat.S_ISREG(s.st_mode) and not p.is_symlink(),'not regular: '+str(p));require(s.st_nlink==1,'hardlink: '+str(p));return s

def main():
 a=argparse.ArgumentParser();a.add_argument('root',type=Path)
 for x in ['final','manifest','report']:a.add_argument('--'+x+'-sha256',required=True)
 args=a.parse_args();r=args.root.absolute()
 require(not r.is_symlink(),'root is a symlink')
 for part in [r,*r.parents]:require(not part.is_symlink(),'symlink in root ancestry')
 for rel,want in [('FINAL.json',args.final_sha256),('packet/MANIFEST.json',args.manifest_sha256),('REPORT.md',args.report_sha256)]:
  require(len(want)==64 and all(c in '0123456789abcdef' for c in want),'invalid anchor')
  regular(r/rel);require(digest(r/rel)==want,'anchor mismatch: '+rel)
 f=json.loads((r/'FINAL.json').read_text());m=json.loads((r/'packet/MANIFEST.json').read_text())
 require(f['manifest_sha256']==args.manifest_sha256,'FINAL manifest binding')
 require(f['report_sha256']==args.report_sha256,'FINAL report binding')
 require(m['schema']=='T088P133-manuscript-review-r1-exact-v1','schema')
 gotfiles=set();gotdirs={'packet'}
 require((r/'packet').is_dir() and not (r/'packet').is_symlink(),'packet root')
 for p in (r/'packet').rglob('*'):
  rel=p.relative_to(r).as_posix();s=p.lstat()
  require(not p.is_symlink(),'symlink: '+rel)
  if stat.S_ISDIR(s.st_mode):gotdirs.add(rel)
  else:regular(p);gotfiles.add(rel)
 require(gotfiles==set(m['files'])|{'packet/MANIFEST.json'},'file set mismatch')
 require(gotdirs==set(m['directories']),'directory set mismatch')
 for rel,v in m['files'].items():
  path=PurePosixPath(rel)
  require(not path.is_absolute() and '..' not in path.parts and rel.startswith('packet/public/'),'unsafe path')
  p=r/rel;s=regular(p)
  require(s.st_size==v['bytes'],'size mismatch: '+rel)
  require(stat.S_IMODE(s.st_mode)==v['mode'],'mode mismatch: '+rel)
  require(digest(p)==v['sha256'],'hash mismatch: '+rel)
 for rel,v in m['directories'].items():
  require(stat.S_IMODE((r/rel).lstat().st_mode)==v['mode'],'directory mode mismatch: '+rel)
 print(json.dumps({'artifact_integrity':'MATCH','files':len(m['files']),'directories':len(m['directories']),'writes_performed':False,'mathematical_gate':False,'scope':'independent final manuscript review artifact only','acceptance':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print('REJECT:',str(e),file=sys.stderr);sys.exit(1)
