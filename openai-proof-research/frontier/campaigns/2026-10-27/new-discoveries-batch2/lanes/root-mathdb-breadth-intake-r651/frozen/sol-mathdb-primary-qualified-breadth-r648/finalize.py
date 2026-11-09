import pathlib,json,hashlib,subprocess,os
P=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(P.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(P)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
r=subprocess.run(['python3','-B',str(P/'verify.py')],capture_output=True,text=True,check=True)
(P/'final-verification-receipt.json').write_text(r.stdout);print(r.stdout)
