import pathlib,json,hashlib,tempfile,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
out={}
with tempfile.TemporaryDirectory(prefix='bounded-negative-',dir=P) as td:
 root=pathlib.Path(td);p=root/'probe';original=b'abc';p.write_bytes(original)
 (root/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':[{'path':'probe','size':3,'sha256':hashlib.sha256(original).hexdigest()}]}))
 def run():return subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--check-payload',str(root)],capture_output=True,text=True,timeout=10)
 assert run().returncode==0
 for name,value in [('hash',b'xbc'),('size',b'abcd')]:
  p.write_bytes(value);r=run();assert r.returncode!=0;out[name+'_rejected']=True;out[name+'_exit']=r.returncode;out[name+'_stderr']=r.stderr.strip()
 p.write_bytes(original);(root/'extra').write_bytes(b'x');r=run();assert r.returncode!=0;out['extra_file_rejected']=True;out['extra_exit']=r.returncode;out['extra_stderr']=r.stderr.strip()
(P/'negative-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
