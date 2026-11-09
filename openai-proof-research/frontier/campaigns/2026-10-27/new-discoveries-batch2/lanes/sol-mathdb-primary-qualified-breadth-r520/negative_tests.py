import pathlib,tempfile,json,hashlib,subprocess,sys
P=pathlib.Path(__file__).resolve().parent;out=[]
for case,err in [('hash','HASH'),('size','SIZE'),('extra','EXTRA_OR_MISSING_FILE')]:
 with tempfile.TemporaryDirectory(prefix='negative-',dir=P) as td:
  root=pathlib.Path(td);p=root/'tiny.txt';p.write_bytes(b'ab')
  (root/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[{'path':'tiny.txt','size':2,'sha256':hashlib.sha256(b'ab').hexdigest()}]}))
  if case=='hash':p.write_bytes(b'ac')
  elif case=='size':p.write_bytes(b'abc')
  else:(root/'unexpected.txt').write_text('extra')
  r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--payload-root',str(root)],capture_output=True,text=True,timeout=10)
  out.append({'case':case,'expected_error':err,'returncode':r.returncode,'output':r.stdout+r.stderr})
  assert r.returncode!=0 and err in out[-1]['output']
(P/'negative-tests.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
