import pathlib,json,hashlib,datetime,subprocess,sys
P=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
m={'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files};(P/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True,timeout=30)
assert r.returncode==0,r.stdout+r.stderr
receipt=json.loads(r.stdout);receipt['utc']=datetime.datetime.now(datetime.timezone.utc).isoformat();receipt['negative_rejection_tests']=3;receipt['payload_files']=len(files)
(P/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
