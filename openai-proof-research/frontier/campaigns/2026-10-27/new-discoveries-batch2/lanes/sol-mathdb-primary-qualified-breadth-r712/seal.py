import pathlib,json,hashlib,tempfile,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
def put(p,x):p.write_text(json.dumps(x,indent=2)+'\n')
f=json.loads((P/'failures.json').read_text());f['failed_helper_runs']=[{'script':'build.py','failure':'ValueError: too many values to unpack (expected6, got8)','cause':'Pipe delimiters in volume formula; corrected textual formula. Local inspect.py name shadowed stdlib inspect during traceback, printing administrative probe output again; renamed probe-schema.py. No scientific conclusion from that output.','guard_exit':1}];put(P/'failures.json',f)
negative=[]
for mode in ['hash','size','extra-file']:
 with tempfile.TemporaryDirectory(prefix='negative-',dir=P) as td:
  t=pathlib.Path(td);b=b'abc';(t/'payload').write_bytes(b)
  put(t/'manifest.json',{'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':[{'path':'payload','size':3,'sha256':hashlib.sha256(b).hexdigest()}]})
  if mode=='hash':(t/'payload').write_bytes(b'abd')
  elif mode=='size':(t/'payload').write_bytes(b'abcd')
  else:(t/'unexpected').write_bytes(b'x')
  r=subprocess.run([sys.executable,'-B',str(P/'verify.py'),'--payload-only',td],capture_output=True,text=True);assert r.returncode!=0
  negative.append({'test':mode,'exit':r.returncode,'stderr':r.stderr.strip(),'isolated_synthetic_payload':True,'originals_mutated':False})
put(P/'negative-tests.json',negative)
exc=['manifest.json','final-verification-receipt.json'];files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and str(p.relative_to(P)) not in exc:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
put(P/'manifest.json',{'excluded_exact_paths':exc,'files':files})
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True)
b=(P/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':r.returncode,'stdout':r.stdout.strip(),'stderr':r.stderr.strip(),'negative_tests':3,'resource_guard':'fixed helper_guard.py; 512MiB AS/groupRSS CPU210s wall230s; unchanged','payload_files':len(files)};put(P/'final-verification-receipt.json',receipt);print(json.dumps(receipt,indent=2));assert r.returncode==0
