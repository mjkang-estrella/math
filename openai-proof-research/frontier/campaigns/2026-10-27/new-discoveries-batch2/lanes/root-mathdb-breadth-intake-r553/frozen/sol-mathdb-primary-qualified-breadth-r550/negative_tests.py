from pathlib import Path
import json,hashlib,subprocess,sys,tempfile
D=Path(__file__).resolve().parent;out=[]
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=D) as tmp:
 t=Path(tmp);p=t/'sample';p.write_bytes(b'fixed')
 m=dict(excluded_exact_paths=['manifest.json','final-verification-receipt.json'],files=[dict(path='sample',size=5,sha256=hashlib.sha256(b'fixed').hexdigest())])
 def run(label):
  r=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--payload-only',str(t)],capture_output=True,text=True);out.append(dict(test=label,exit_code=r.returncode,stdout=r.stdout,stderr=r.stderr));return r.returncode
 (t/'manifest.json').write_text(json.dumps(m));assert run('clean fixture')==0
 p.write_bytes(b'fixee');assert run('same-size hash mutation rejected')!=0
 p.write_bytes(b'fixed!');assert run('size mutation rejected')!=0
 p.write_bytes(b'fixed');(t/'unexpected').write_bytes(b'x');assert run('extra file rejected')!=0
(D/'negative-test-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
