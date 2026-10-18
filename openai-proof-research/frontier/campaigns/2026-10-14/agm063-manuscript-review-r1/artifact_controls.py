"""Independent controls of the sealed manuscript's actual verifier; MIT."""
import hashlib,json,os,shutil,subprocess,sys,tempfile
from pathlib import Path
R=Path(__file__).resolve().parent;P=R.parent/'agm063-manuscript-r1'
A='5a043ad5acdf541b9a10d912dbd0339b3c8c0aa2650bd92a4a41d5422d0c34bb'
def snap(p):return {x.relative_to(p).as_posix():hashlib.sha256(x.read_bytes()).hexdigest() for x in p.rglob('*') if x.is_file()}
before=snap(P);rows=[]
def call(n,root,a,w):
 p=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--root',str(root),'--anchor',a],capture_output=True,text=True)
 assert (p.returncode==0)==w,(n,p.stdout,p.stderr)
 rows.append(dict(name=n,exit=p.returncode,stdout=p.stdout,stderr=p.stderr))
call('original-positive',P,A,True);call('wrong-anchor',P,'0'*64,False)
with tempfile.TemporaryDirectory(prefix='.tamper-',dir=R) as tmp:
 t=Path(tmp)/'packet';shutil.copytree(P,t)
 def check(n,w=False,a=A):call(n,t,a,w)
 check('exact-copy',True)
 p=t/'main.tex';old=p.read_bytes();p.write_bytes(old+b'\n');check('changed-main');p.write_bytes(old)
 p.unlink();check('missing-main');p.write_bytes(old)
 x=t/'extra';x.write_text('x');check('extra-file');x.unlink();x.mkdir();check('extra-directory');x.rmdir()
 p.unlink();p.symlink_to(P/'main.tex');check('symlink-file');p.unlink();p.write_bytes(old)
 x.symlink_to(P/'checks',target_is_directory=True);check('symlink-directory');x.unlink()
 os.link(p,x);check('hardlink');x.unlink()
 os.mkfifo(x);check('fifo');x.unlink()
 # Local manifest rehash cannot replace the external root pin.
 m=t/'output-manifest.json';raw=m.read_bytes();p.write_bytes(old+b'\n');data=json.loads(raw)
 for row in data['files']:
  if row['path']=='main.tex':row['bytes']=len(p.read_bytes());row['sha256']=hashlib.sha256(p.read_bytes()).hexdigest()
 m.write_text(json.dumps(data,indent=2)+'\n');check('locally-rehashed-tamper-original-anchor');m.write_bytes(raw);p.write_bytes(old)
 check('restored',True)
call('original-final-positive',P,A,True)
assert before==snap(P)
(R/'artifact-controls.json').write_text(json.dumps(dict(status='PASS_INDEPENDENT_MANUSCRIPT_CONTROLS',original_before_after_identical=True,rows=rows),indent=2)+'\n')
print('PASS_INDEPENDENT_MANUSCRIPT_CONTROLS',len(rows))
