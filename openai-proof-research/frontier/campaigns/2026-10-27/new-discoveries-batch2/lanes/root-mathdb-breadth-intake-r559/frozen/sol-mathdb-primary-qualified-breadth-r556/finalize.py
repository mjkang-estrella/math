import pathlib,json,hashlib,subprocess,sys,datetime
P=pathlib.Path(__file__).resolve().parent
receipt=P/'final-verification-receipt.json';receipt.write_text('{}\n')
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and str(p.relative_to(P)) not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
m=P/'manifest.json';m.write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},sort_keys=True,indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True)
b=m.read_bytes();result={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'payload_files':len(files),'negative_tests':json.loads((P/'negative-test-results.json').read_text()),'integrity':'PASS' if r.returncode==0 else 'FAIL','scientific_acceptance':False,'registry_clearance':False}
receipt.write_text(json.dumps(result,sort_keys=True,indent=2)+'\n');print(json.dumps(result,indent=2));sys.exit(r.returncode)
