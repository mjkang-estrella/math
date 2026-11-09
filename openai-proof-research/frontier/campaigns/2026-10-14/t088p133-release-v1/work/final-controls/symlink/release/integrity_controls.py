#!/usr/bin/env python3
# Copyright (c) 2026 Myeongjin Kang. MIT; see packet/public/LICENSE-CODE.txt.
"""Copy-only integrity controls. Authenticate this program before running.
Writes only to a new specified output tree, never changes the extracted artifact.
"""
import argparse,hashlib,importlib.util,json,os,shutil,stat,subprocess,sys,zipfile
from pathlib import Path
sys.dont_write_bytecode=True
def req(ok,msg):
 if not ok:raise ValueError(msg)
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def snap(root):
 r={}
 for d,ds,fs in os.walk(root,followlinks=False):
  for n in ds+fs:
   p=Path(d)/n;s=p.lstat();v={'mode':s.st_mode,'links':s.st_nlink}
   if p.is_symlink():v['target']=os.readlink(p)
   elif p.is_file():v['sha256']=sha(p)
   r[p.relative_to(root).as_posix()]=v
 return r
def write(p,b):
 p.chmod(0o644);p.write_bytes(b);p.chmod(0o444)
def main():
 ap=argparse.ArgumentParser(description=__doc__);ap.add_argument('--root',type=Path,required=True);ap.add_argument('--output',type=Path,required=True)
 for n in ['final','manifest','report','archive']:
  ap.add_argument('--'+n,type=Path,required=True);ap.add_argument('--'+n+'-sha256',required=True)
 a=ap.parse_args();root=a.root.resolve();out=a.output.absolute();req(not out.exists() and not out.is_symlink() and not out.is_relative_to(root) and not root.is_relative_to(out),'fresh nonoverlapping output')
 for p in out.parents:req(not p.is_symlink(),'symlink output ancestry')
 verifier=root/'verify.py';base=[sys.executable,'-B',str(verifier)]
 for n in ['final','manifest','report','archive']:base+=['--'+n,str(getattr(a,n).resolve()),'--'+n+'-sha256',getattr(a,n+'_sha256')]
 # The entire real extraction is externally authenticated before loading any helper.
 subprocess.run(base+['--root',str(root)],check=True,capture_output=True,text=True)
 before=snap(root);out.mkdir(parents=True);results=[]
 cases=['intact','wrong_external_final','changed_file','missing_file','extra_file','extra_directory','symlink','hardlink','file_mode','directory_mode','forged_local_reseal','changed_archive','missing_zip_member','extra_zip_member']
 for label in cases:
  c=out/label;c.mkdir();target=c/'release';shutil.copytree(root,target);args=base+['--root',str(target)];p=target/'README.md'
  if label=='wrong_external_final':args[args.index('--final-sha256')+1]='0'*64
  elif label=='changed_file':write(p,p.read_bytes()+b'changed\n')
  elif label=='missing_file':p.unlink()
  elif label=='extra_file':(target/'EXTRA').write_text('extra')
  elif label=='extra_directory':(target/'EXTRA').mkdir()
  elif label=='symlink':p.unlink();p.symlink_to('packet/public/main.tex')
  elif label=='hardlink':p.unlink();os.link(target/'packet/public/main.tex',p)
  elif label=='file_mode':p.chmod(0o644)
  elif label=='directory_mode':(target/'packet').chmod(0o700)
  elif label=='forged_local_reseal':
   write(p,p.read_bytes()+b'forged\n');m=json.loads((target/'MANIFEST.json').read_text());m['files']['README.md'].update(sha256=sha(p),bytes=p.stat().st_size)
   write(target/'MANIFEST.json',(json.dumps(m,indent=2,sort_keys=True)+'\n').encode());forged=c/'MANIFEST.json';shutil.copyfile(target/'MANIFEST.json',forged)
   f=json.loads(a.final.read_text());f['manifest_sha256']=sha(forged);ff=c/'FINAL.json';ff.write_text(json.dumps(f,sort_keys=True)+'\n');args[args.index('--final')+1]=str(ff);args[args.index('--manifest')+1]=str(forged)
  elif label in ['changed_archive','missing_zip_member','extra_zip_member']:
   z=c/'mutated.zip'
   if label=='changed_archive':shutil.copyfile(a.archive,z);z.write_bytes(z.read_bytes()+b'changed')
   else:
    with zipfile.ZipFile(a.archive) as original,zipfile.ZipFile(z,'w') as new:
     for i in original.infolist():
      if label=='missing_zip_member' and i.filename=='README.md':continue
      new.writestr(i,original.read(i))
     if label=='extra_zip_member':new.writestr('extra',b'x')
   args[args.index('--archive')+1]=str(z)
  fixture=snap(c);r=subprocess.run(args,capture_output=True,text=True);preserved=snap(c)==fixture
  req(preserved,'verifier mutated fixture '+label);req((r.returncode==0)==(label=='intact'),'unexpected exit '+label)
  results.append({'case':label,'exit':r.returncode,'expected_pass':label=='intact','fixture_unchanged':preserved,'stdout':r.stdout,'stderr':r.stderr})
 # Exercise the ZIP structural checks separately, bypassing the earlier SHA rejection.
 # These are parser-unit controls, not acceptance of altered archives under old anchors.
 spec=importlib.util.spec_from_file_location('trusted_verifier',verifier);v=importlib.util.module_from_spec(spec);spec.loader.exec_module(v)
 m=json.loads(a.manifest.read_text());mb=a.manifest.read_bytes();parser=[]
 for label in ['duplicate','absolute','dotdot','zip_symlink','zip_mode','zip_extra','zip_missing']:
  z=out/(label+'.zip')
  with zipfile.ZipFile(a.archive) as original,zipfile.ZipFile(z,'w') as new:
   for i in original.infolist():
    if label=='zip_missing' and i.filename=='README.md':continue
    if i.filename=='README.md' and label in ['zip_symlink','zip_mode']:
     i.external_attr=((stat.S_IFLNK|0o777) if label=='zip_symlink' else (stat.S_IFREG|0o644))<<16
    new.writestr(i,original.read(i.filename))
   if label=='duplicate':new.writestr('README.md',b'duplicate')
   elif label=='absolute':new.writestr('/escape',b'x')
   elif label=='dotdot':new.writestr('../escape',b'x')
   elif label=='zip_extra':new.writestr('extra',b'x')
  beforezip=sha(z)
  try:v.check_zip(z,m,mb)
  except (ValueError,zipfile.BadZipFile) as error:parser.append({'case':label,'rejected':True,'reason':str(error),'archive_unchanged':sha(z)==beforezip})
  else:raise ValueError('parser accepted '+label)
 req(snap(root)==before,'real extraction changed')
 result={'cases':results,'parser_controls':parser,'all_expected':True,'real_extraction_unchanged':True,'scope':'Integrity only; no mathematical/release/acceptance gate.'}
 (out/'receipt.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps({'cases':len(results),'parser_controls':len(parser),'all_expected':True,'real_extraction_unchanged':True}))
if __name__=='__main__':main()
