import tempfile,pathlib,json,hashlib,subprocess,sys
O=pathlib.Path(__file__).resolve().parent
results=[]
with tempfile.TemporaryDirectory(dir=O,prefix='negative-fixture-') as tmp:
 p=pathlib.Path(tmp);b=b'abc';(p/'sample').write_bytes(b)
 m={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[{'path':'sample','size':3,'sha256':hashlib.sha256(b).hexdigest()}]}
 (p/'manifest.json').write_text(json.dumps(m))
 def run():return subprocess.run([sys.executable,'-B',str(O/'verify.py'),'--payload-root',str(p)],capture_output=True,text=True)
 assert run().returncode==0
 for kind,data in [('hash',b'abd'),('size',b'abcd'),('extra_file',b'abc')]:
  (p/'sample').write_bytes(data)
  if kind=='extra_file':(p/'unexpected').write_bytes(b'x')
  r=run();assert r.returncode!=0,(kind,r.stdout)
  results.append({'mutation':kind,'exit_code':r.returncode,'stderr':r.stderr.strip(),'rejected':True})
(O/'negative-tests.json').write_text(json.dumps({'originals_mutated':False,'bounded_fixture_tests':results},indent=2)+'\n');print(json.dumps(results))
