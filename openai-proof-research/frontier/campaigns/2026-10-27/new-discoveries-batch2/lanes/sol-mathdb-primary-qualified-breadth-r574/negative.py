import pathlib,tempfile,json,hashlib,subprocess,sys
P=pathlib.Path(__file__).parent;results={}
for case in ['control','hash','size','extra']:
 with tempfile.TemporaryDirectory(prefix='negative-',dir=P) as tmp:
  p=pathlib.Path(tmp);b=b'bound fixture\n';(p/'data').write_bytes(b)
  e={'path':'data','size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
  if case=='hash':e['sha256']='0'*64
  if case=='size':e['size']+=1
  if case=='extra':(p/'unlisted').write_bytes(b'x')
  (p/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[e]}))
  r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--fixture',str(p)],capture_output=True,text=True)
  results[case]={'exit_code':r.returncode,'stdout':r.stdout,'stderr':r.stderr}
assert results['control']['exit_code']==0 and all(results[k]['exit_code']!=0 for k in ['hash','size','extra'])
(P/'negative-test-results.json').write_text(json.dumps(results,indent=2)+'\n');print(json.dumps(results))
