import pathlib,tempfile,json,hashlib,subprocess,sys
P=pathlib.Path(__file__).resolve().parent;out=[]
for kind in ['control','hash','size','extra-file']:
 with tempfile.TemporaryDirectory(dir=P,prefix='negative-fixture-') as d:
  p=pathlib.Path(d);b=b'bounded own-lane test\n';(p/'payload').write_bytes(b)
  e={'path':'payload','size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
  if kind=='hash':e['sha256']='0'*64
  if kind=='size':e['size']+=1
  if kind=='extra-file':(p/'unexpected').write_text('x')
  (p/'manifest.json').write_text(json.dumps({'files':[e],'excluded_exact_paths':['manifest.json']}))
  r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--payload-only',str(p)],capture_output=True,text=True)
  assert (r.returncode==0)==(kind=='control')
  out.append({'test':kind,'exit':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip(),'passed':True})
(P/'negative-test-results.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
