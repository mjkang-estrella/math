import pathlib,json,hashlib,datetime,subprocess,sys
D=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
m={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files}
(D/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
r=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
b=(D/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':{'path':'manifest.json','size':len(b),'sha256':hashlib.sha256(b).hexdigest()},'verifier_exit':r.returncode,'verifier_stdout':r.stdout,'verifier_stderr':r.stderr,'negative_tests':json.loads((D/'negative-test-results.json').read_text()),'integrity_is_not_math_or_novelty_pass':True}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(r.returncode)
