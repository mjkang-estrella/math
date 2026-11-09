import pathlib,json,hashlib,subprocess,sys,tempfile
D=pathlib.Path(__file__).resolve().parent
results=[]
with tempfile.TemporaryDirectory(prefix='negative-fixture-',dir=D) as folder:
 P=pathlib.Path(folder);b=b'abcd';(P/'payload').write_bytes(b)
 m={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[{'path':'payload','size':4,'sha256':hashlib.sha256(b).hexdigest()}]}
 (P/'manifest.json').write_text(json.dumps(m))
 def run(name,expected):
  p=subprocess.run([sys.executable,'-B',str(D/'verify.py'),'--payload-only',str(P)],capture_output=True,text=True)
  assert (p.returncode==0)==expected,(name,p.stdout,p.stderr)
  results.append({'test':name,'exit':p.returncode,'stdout':p.stdout.strip(),'stderr':p.stderr.strip()})
 run('valid control',True)
 (P/'payload').write_bytes(b'abce');run('same-size hash corruption rejected',False)
 (P/'payload').write_bytes(b'abcde');run('size corruption rejected',False)
 (P/'payload').write_bytes(b);(P/'unexpected').write_bytes(b'x');run('extra file rejected',False)
(D/'negative-test-results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
