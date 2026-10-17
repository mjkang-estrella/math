import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
R=Path(__file__).resolve().parent;P=R.parent/'agm063-formal-v1'
A='ca6bdb0cccd691d0c8a94ff8ec3bfbd9ccdd87a64ba5b4cf344a1b1c73b8ad9c'
rows=[]
def call(name,cmd,want):
 p=subprocess.run(cmd,capture_output=True,text=True)
 assert (p.returncode==0)==want,(name,p.stdout,p.stderr)
 rows.append(dict(name=name,command=cmd,exit=p.returncode,stdout=p.stdout,stderr=p.stderr))
with tempfile.TemporaryDirectory(prefix='.fixture-',dir=R) as tmp:
 t=Path(tmp)/'packet';shutil.copytree(P,t)
 def verify(name,want=True,anchor=A):call(name,[sys.executable,'-B',str(P/'verify.py'),'--root',str(t),'--anchor',anchor],want)
 verify('exact-copy');verify('wrong-anchor',False,'0'*64)
 p=t/'AGM063.lean';old=p.read_bytes();p.write_bytes(old+b'\n');verify('changed-source',False);p.write_bytes(old)
 p.unlink();verify('missing-source',False);p.write_bytes(old)
 extra=t/'unexpected';extra.write_text('x');verify('extra-file',False);extra.unlink()
 extra.mkdir();verify('extra-directory',False);extra.rmdir()
 p.unlink();p.symlink_to(P/'AGM063.lean');verify('symlink-file',False);p.unlink();p.write_bytes(old)
 d=t/'mutants';d.rename(t/'mutants-saved');d.symlink_to(t/'mutants-saved',target_is_directory=True);verify('symlink-directory',False);d.unlink();(t/'mutants-saved').rename(d)
 verify('restored-copy')
 logs=R/'wrapper-logs';logs.mkdir(exist_ok=True)
 for name,code,want in [('stdout-failure',"print('SOME FAIL')",False),('stderr-failure',"import sys;sys.stderr.write('error: sentinel')",False),('nonzero',"raise SystemExit(9)",False),('clean',"print('independent clean child')",True)]:
  call(name,[sys.executable,'-B',str(P/'checked_run.py'),'--log-prefix',str(logs/name),'--',sys.executable,'-c',code],want)
call('original-post-check',[sys.executable,'-B',str(P/'verify.py'),'--anchor',A],True)
(R/'artifact-controls.json').write_text(json.dumps({'result':'PASS_ARTIFACT_CONTROLS','rows':rows},indent=2)+'\n')
print('PASS_ARTIFACT_CONTROLS')
