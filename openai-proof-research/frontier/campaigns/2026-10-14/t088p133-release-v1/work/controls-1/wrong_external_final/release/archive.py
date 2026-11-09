#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT; see packet/public/LICENSE-CODE.txt.
"""Explicit writing operations after external verification. Output must be NEW.
Assemble fixed ZIP from declared source, or safely extract expected members.
This program does not establish trust: first run externally anchored verify.py.
"""
import argparse,hashlib,json,os,stat,sys,zipfile
from pathlib import Path,PurePosixPath
sys.dont_write_bytecode=True
STAMP=(2026,10,20,0,0,0)
def req(ok,msg):
 if not ok:raise ValueError(msg)
def sha(b):return hashlib.sha256(b).hexdigest()
def safe(p):
 req(p and not PurePosixPath(p).is_absolute() and str(PurePosixPath(p))==p and '..' not in p.split('/') and '.' not in p.split('/') and '\\' not in p and ':' not in p,'unsafe path')
def fresh(p):
 req(not p.exists() and not p.is_symlink(),'output must be fresh')
 for q in p.parents:req(not q.is_symlink(),'output ancestor symlink')
 p.mkdir(parents=True);p.chmod(0o755)
def source_inventory(p):
 files={};dirs={}
 for d,ds,fs in os.walk(p,followlinks=False):
  for n in ds+fs:
   q=Path(d)/n;rel=q.relative_to(p).as_posix();safe(rel);st=q.lstat();req(not q.is_symlink(),'symlink source')
   if q.is_dir():dirs[rel]=stat.S_IMODE(st.st_mode)
   else:
    req(stat.S_ISREG(st.st_mode) and st.st_nlink==1,'special source');files[rel]={'sha256':sha(q.read_bytes()),'bytes':st.st_size,'mode':stat.S_IMODE(st.st_mode)}
 return files,dirs
def main():
 ap=argparse.ArgumentParser(description=__doc__);sub=ap.add_subparsers(dest='action',required=True)
 a=sub.add_parser('assemble');a.add_argument('--source',type=Path,required=True);a.add_argument('--output',type=Path,required=True)
 e=sub.add_parser('extract');e.add_argument('--archive',type=Path,required=True);e.add_argument('--manifest',type=Path,required=True);e.add_argument('--output',type=Path,required=True)
 x=ap.parse_args();out=x.output.absolute()
 if x.action=='assemble':
  src=x.source.absolute();req(not out.is_relative_to(src) and not src.is_symlink(),'output/source overlap')
  mb=(src/'MANIFEST.json').read_bytes();m=json.loads(mb);fs,ds=source_inventory(src)
  expected=dict(m['files']);expected['MANIFEST.json']={'sha256':sha(mb),'bytes':len(mb),'mode':0o444}
  req(fs==expected and ds==m['directories'],'source differs from manifest')
  fresh(out);names=sorted(set(fs)|{p+'/' for p in ds})
  with zipfile.ZipFile(out/'release.zip','w',compression=zipfile.ZIP_STORED,allowZip64=False) as z:
   for name in names:
    directory=name.endswith('/');i=zipfile.ZipInfo(name,STAMP);i.create_system=3;i.compress_type=zipfile.ZIP_STORED;i.external_attr=((stat.S_IFDIR|0o755)<<16)|0x10 if directory else (stat.S_IFREG|0o444)<<16
    z.writestr(i,b'' if directory else (src/name).read_bytes())
  print(json.dumps({'archive_sha256':sha((out/'release.zip').read_bytes()),'entries':len(names),'output':str(out/'release.zip')}))
 else:
  mb=x.manifest.read_bytes();m=json.loads(mb);expected=set(m['files'])|{'MANIFEST.json'}|{p+'/' for p in m['directories']}
  with zipfile.ZipFile(x.archive) as z:
   infos=z.infolist();names=[i.filename for i in infos];req(len(names)==len(set(names)) and set(names)==expected,'member set')
   for i in infos:
    name=i.filename;directory=name.endswith('/');safe(name[:-1] if directory else name)
    req((i.external_attr>>16)==(stat.S_IFDIR|0o755 if directory else stat.S_IFREG|0o444),'member type/mode')
    b=z.read(i)
    if directory:req(not b,'directory contents')
    elif name=='MANIFEST.json':req(b==mb,'manifest bytes')
    else:req(len(b)==m['files'][name]['bytes'] and sha(b)==m['files'][name]['sha256'],'member bytes')
   fresh(out)
   for name in sorted(m['directories'],key=lambda p:(p.count('/'),p)):
    (out/name).mkdir();(out/name).chmod(0o755)
   for name in sorted(set(m['files'])|{'MANIFEST.json'}):
    p=out/name
    with p.open('xb') as f:f.write(z.read(name))
    p.chmod(0o444)
  print(json.dumps({'extracted_files':len(m['files'])+1,'directories':len(m['directories']),'root':str(out)}))
if __name__=='__main__':main()
