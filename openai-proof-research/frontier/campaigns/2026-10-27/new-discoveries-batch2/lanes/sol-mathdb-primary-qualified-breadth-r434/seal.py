from pathlib import Path
import hashlib,json,subprocess,sys,datetime
O=Path(__file__).resolve().parent
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in {'manifest.json','final-receipt.json'}:
  files.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
(O/'manifest.json').write_text(json.dumps({'files':files},indent=2)+'\n')
p=subprocess.run([sys.executable,'-B',str(O/'verify.py')],capture_output=True,text=True)
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'exit_code':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'manifest_sha256':hashlib.sha256((O/'manifest.json').read_bytes()).hexdigest(),'exclusions_exact_relative_paths':['manifest.json','final-receipt.json']}
(O/'final-receipt.json').write_text(json.dumps(r,indent=2)+'\n')
print(json.dumps(r));sys.exit(p.returncode)
