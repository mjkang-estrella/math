import json,shutil,subprocess,sys,tempfile
from pathlib import Path
from seal import seal
R=Path(__file__).resolve().parent
entries=list(R.iterdir());rows=[]
with tempfile.TemporaryDirectory(prefix='.seal-fixture-',dir=R) as tmp:
 t=Path(tmp)/'packet';t.mkdir()
 for p in entries:
  if p.is_dir():shutil.copytree(p,t/p.name)
  else:shutil.copy2(p,t/p.name)
 a=seal(t)
 def check(n,w=True,anchor=a):
  p=subprocess.run([sys.executable,'-B',str(R/'verify.py'),'--root',str(t),'--anchor',anchor],capture_output=True,text=True)
  assert (p.returncode==0)==w,(n,p.stdout,p.stderr)
  rows.append(dict(name=n,exit=p.returncode,stdout=p.stdout,stderr=p.stderr))
 check('positive');check('wrong-anchor',False,'0'*64)
 p=t/'review.md';old=p.read_bytes();p.write_bytes(old+b'\n');check('changed',False);p.write_bytes(old)
 p.unlink();check('missing',False);p.write_bytes(old)
 x=t/'extra';x.write_text('x');check('extra-file',False);x.unlink();x.mkdir();check('extra-directory',False);x.rmdir()
 p.unlink();p.symlink_to(R/'review.md');check('symlink',False);p.unlink();p.write_bytes(old)
 check('restored')
(R/'review-verifier-controls.json').write_text(json.dumps(dict(result='PASS_REVIEW_VERIFIER_CONTROLS',fixture_anchor=a,rows=rows),indent=2)+'\n')
print('PASS_REVIEW_VERIFIER_CONTROLS')
