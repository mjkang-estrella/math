from pathlib import Path
import tempfile,shutil,subprocess,sys,json
D=Path(__file__).resolve().parent;out=[]
# Copy ONLY this lane's payload for mutations, never corpus or historical trees.
with tempfile.TemporaryDirectory(prefix='negative-',dir=D) as td:
 T=Path(td)
 for p in D.iterdir():
  if p.is_file():shutil.copyfile(p,T/p.name)
 def run(case):
  r=subprocess.run([sys.executable,'-B',str(T/'verify.py'),str(T)],capture_output=True,text=True);out.append(dict(case=case,exit=r.returncode,stdout=r.stdout,stderr=r.stderr));return r.returncode
 assert run('unmodified control')==0
 p=T/'proposals.json';b=p.read_bytes();p.write_bytes(b.replace(b'[',b'{',1));assert run('same-size SHA256 corruption')!=0;p.write_bytes(b)
 p.write_bytes(b+b' ');assert run('size corruption')!=0;p.write_bytes(b)
 p=T/'unexpected-payload';p.write_text('extra');assert run('extra file')!=0;p.unlink()
 assert run('restored control')==0
(D/'negative-test-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
