#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT License; see packet/public/LICENSE-CODE.txt.
"""Read-only exact archive/extraction verification. Requires four EXTERNAL anchors.
No payload execution, extraction, network, subprocesses, cache or report writes.
"""
import argparse,hashlib,json,os,stat,sys,zipfile
from pathlib import Path,PurePosixPath
sys.dont_write_bytecode=True
STAMP=(2026,10,20,0,0,0)
def require(ok,msg):
 if not ok:raise ValueError(msg)
def digest(b):return hashlib.sha256(b).hexdigest()
def safe(name):
 require(isinstance(name,str) and bool(name) and '\\' not in name and '\x00' not in name,'unsafe path')
 p=PurePosixPath(name);require(not p.is_absolute() and '..' not in p.parts and '.' not in name.split('/') and '' not in name.split('/') and ':' not in name,'unsafe path '+name)
 require(str(p)==name,'noncanonical path '+name)
def regular(p):
 for part in [p,*p.parents]:require(not part.is_symlink(),'symlink '+str(part))
 s=p.lstat();require(stat.S_ISREG(s.st_mode) and s.st_nlink==1,'not single regular file '+str(p));return s
def raw(p):regular(p);return p.read_bytes()
def check_root(root,m,mb):
 require(root.is_dir() and not root.is_symlink(),'root directory')
 for part in root.parents:require(not part.is_symlink(),'root ancestry symlink')
 require(stat.S_IMODE(root.stat().st_mode)==0o755,'root mode')
 files={};dirs={}
 for d,ds,fs in os.walk(root,followlinks=False):
  for name in ds+fs:
   p=Path(d)/name;rel=p.relative_to(root).as_posix();safe(rel);s=p.lstat();require(not p.is_symlink(),'symlink '+rel)
   if stat.S_ISDIR(s.st_mode):dirs[rel]=stat.S_IMODE(s.st_mode)
   else:regular(p);files[rel]=p
 require(set(files)==set(m['files'])|{'MANIFEST.json'},'file set mismatch')
 require(dirs==m['directories'],'directory set/mode mismatch')
 require(raw(files['MANIFEST.json'])==mb,'embedded manifest mismatch')
 require(stat.S_IMODE(files['MANIFEST.json'].stat().st_mode)==0o444,'manifest mode')
 for name,v in m['files'].items():
  p=files[name];s=p.stat();require(s.st_size==v['bytes'] and stat.S_IMODE(s.st_mode)==v['mode'] and digest(raw(p))==v['sha256'],'file mismatch '+name)
def check_zip(path,m,mb):
 expected={p+'/' for p in m['directories']}|set(m['files'])|{'MANIFEST.json'}
 with zipfile.ZipFile(path) as z:
  entries=z.infolist();names=[i.filename for i in entries]
  require(len(set(names))==len(names),'duplicate ZIP member')
  require(set(names)==expected and names==sorted(expected),'ZIP exact member set/order')
  require(z.comment==b'','ZIP comment')
  for i in entries:
   name=i.filename;isdir=name.endswith('/');safe(name[:-1] if isdir else name)
   mode=stat.S_IFDIR|0o755 if isdir else stat.S_IFREG|0o444
   require(i.create_system==3 and i.external_attr==((mode<<16)|(0x10 if isdir else 0)),'ZIP mode/type '+name)
   require(i.date_time==STAMP and i.compress_type==zipfile.ZIP_STORED and i.flag_bits==0 and not i.extra and not i.comment,'ZIP metadata '+name)
   require(i.compress_size==i.file_size,'ZIP stored size '+name)
   data=z.read(i)
   if isdir:require(data==b'','directory body')
   elif name=='MANIFEST.json':require(data==mb,'ZIP manifest mismatch')
   else:
    v=m['files'][name];require(len(data)==v['bytes'] and digest(data)==v['sha256'],'ZIP bytes '+name)
 return len(entries)
def main():
 ap=argparse.ArgumentParser(description=__doc__)
 for name in ['final','manifest','report','archive']:
  ap.add_argument('--'+name,type=Path,required=True);ap.add_argument('--'+name+'-sha256',required=True)
 ap.add_argument('--root',type=Path);a=ap.parse_args();blobs={}
 for name in ['final','manifest','report','archive']:
  want=getattr(a,name+'_sha256');require(len(want)==64 and all(c in '0123456789abcdef' for c in want),'invalid external anchor')
  b=raw(getattr(a,name));require(digest(b)==want,'external '+name+' anchor mismatch');blobs[name]=b
 f=json.loads(blobs['final']);m=json.loads(blobs['manifest'])
 require(f['schema']=='T088P133-portable-local-release-final-v1' and m['schema']=='T088P133-portable-local-release-manifest-v1','schema')
 for name in ['manifest','report','archive']:require(f[name+'_sha256']==getattr(a,name+'_sha256'),'FINAL binding '+name)
 require(f['verifier_sha256']==digest(raw(Path(__file__).absolute())),'trusted verifier differs from FINAL')
 for p,v in m['files'].items():safe(p);require(v['mode']==0o444 and v['bytes']>=0,'manifest metadata')
 for p,v in m['directories'].items():safe(p);require(v==0o755,'directory metadata')
 require('MANIFEST.json' not in m['files'],'manifest self-entry')
 count=check_zip(a.archive,m,blobs['manifest'])
 if a.root:check_root(a.root.absolute(),m,blobs['manifest'])
 print(json.dumps({'artifact_integrity':'MATCH','payload_files':len(m['files']),'archive_files':len(m['files'])+1,'directories':len(m['directories']),'zip_entries':count,'extracted_root_checked':bool(a.root),'writes_performed':False,'gate_assigned':False}))
if __name__=='__main__':
 try:main()
 except Exception as e:print('REJECT: '+str(e),file=sys.stderr);sys.exit(1)
