#!/usr/bin/env python3
# Copyright 2026 Myeongjin Kang. MIT.
"""Independent wrapper and integrity negatives, exclusively in this review dir."""
from pathlib import Path
import hashlib,json,os,shutil,subprocess,sys,tempfile
R=Path(__file__).resolve().parent
P=R/'private/formal'
A='510548427d70b08ff90285e1ec90ba71cb29905a5ba674ce37902a6ff789cbef'
def main():
 out=R/'checks';out.mkdir(exist_ok=True)
 env=dict(os.environ);env['PYTHONDONTWRITEBYTECODE']='1'
 rows=[]
 command=[sys.executable,'-B',str(P/'checked_run.py'),'--log-prefix',str(out/'marker-child'),'--',sys.executable,'-c','print("SOME FAIL")']
 p=subprocess.run(command,cwd=R,env=env,capture_output=True,text=True)
 (out/'wrapper.stdout').write_text(p.stdout);(out/'wrapper.stderr').write_text(p.stderr)
 assert p.returncode!=0 and (out/'marker-child.stdout').read_text()=='SOME FAIL\n' and 'exit=0' in p.stderr
 rows.append({'case':'zero-exit-SOME-FAIL','wrapper_exit':p.returncode,'child_exit_verified_by_wrapper_message':0,'result':'REJECTED'})
 m=json.loads((P/'output-manifest.json').read_text())
 with tempfile.TemporaryDirectory(prefix='.integrity-',dir=R) as td:
  q=Path(td)
  for e in m['files']:
   d=q/e['path'];d.parent.mkdir(parents=True,exist_ok=True);d.write_bytes((P/e['path']).read_bytes())
  (q/'output-manifest.json').write_bytes((P/'output-manifest.json').read_bytes())
  def check(label,anchor,success=False,reason=None):
   run=subprocess.run([sys.executable,'-I',str(q/'verify.py'),'--anchor',anchor],env=env,capture_output=True,text=True)
   (out/(label+'.stdout')).write_text(run.stdout);(out/(label+'.stderr')).write_text(run.stderr)
   assert (run.returncode==0)==success,(label,run.stdout,run.stderr)
   if reason:assert reason in run.stderr,(label,run.stderr)
   rows.append({'case':label,'exit_code':run.returncode,'result':'ACCEPTED' if success else 'REJECTED','required_reason':reason})
  check('identity-positive',A,True)
  check('wrong-anchor','0'*64,reason='external manifest anchor mismatch')
  (q/'extra.txt').write_text('unexpected member\n');check('extra-member',A,reason='exact file membership mismatch');(q/'extra.txt').unlink()
  original=(q/'CDFLocal.lean').read_bytes();(q/'CDFLocal.lean').write_bytes(original+b'\n')
  check('changed-source',A,reason='changed payload: CDFLocal.lean');(q/'CDFLocal.lean').write_bytes(original)
  (q/'CDFLocal.lean').unlink();check('missing-source',A,reason='exact file membership mismatch');(q/'CDFLocal.lean').write_bytes(original)
  check('identity-restored',A,True)
 (out/'independent-controls.json').write_text(json.dumps({'formal_anchor':A,'cases':rows,'writes_outside_review':False},indent=2)+'\n')
 print(json.dumps({'result':'PASS independent wrapper and identity controls','cases':len(rows)}))
if __name__=='__main__':main()
