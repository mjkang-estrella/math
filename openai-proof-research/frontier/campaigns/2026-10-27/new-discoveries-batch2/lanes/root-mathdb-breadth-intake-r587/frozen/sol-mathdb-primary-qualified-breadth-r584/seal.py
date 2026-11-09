from pathlib import Path
import hashlib,json,subprocess,sys,datetime
D=Path(__file__).parent
ex=['manifest.json','final-verification-receipt.json'];files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in ex:
  b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'manifest.json').write_text(json.dumps({'files':files,'excluded_exact_paths':ex},indent=2)+'\n')
r=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True)
b=(D/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'exit':r.returncode,'stdout':r.stdout,'stderr':r.stderr,'negative_tests':json.loads((D/'negative-tests.json').read_text()),'guard':'fixed helper_guard.py outer process; 512MiB AS/groupRSS CPU210 wall230'}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt,indent=2));sys.exit(r.returncode)
