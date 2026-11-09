import pathlib,json,hashlib,subprocess,datetime,sys
D=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
p=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
b=(D/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit':p.returncode,'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'stdout':p.stdout,'stderr':p.stderr,'scientific_acceptance':False,'registry':'HOLD'}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));sys.exit(p.returncode)
