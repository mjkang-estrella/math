from pathlib import Path
import tempfile,json,hashlib,subprocess,sys
D=Path(__file__).resolve().parent
out=[]
with tempfile.TemporaryDirectory(dir=D,prefix='negative-fixture-') as t:
 p=Path(t);f=p/'x';f.write_bytes(b'abc');m={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[{'path':'x','size':3,'sha256':hashlib.sha256(b'abc').hexdigest()}]}
 def run(name):
  r=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--payload-only',str(p)],capture_output=True,text=True);out.append({'test':name,'exit':r.returncode,'output':(r.stdout+r.stderr).strip()});return r.returncode
 (p/'manifest.json').write_text(json.dumps(m));assert run('positive_fixture')==0
 f.write_bytes(b'abd');assert run('same_size_hash_mismatch')!=0
 f.write_bytes(b'abcd');assert run('size_mismatch')!=0
 f.write_bytes(b'abc');(p/'extra').write_text('x');assert run('extra_file')!=0
(D/'negative-tests.json').write_text(json.dumps({'tests':out,'originals_mutated':False,'fixture_removed':True},indent=2)+'\n')
