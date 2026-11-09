from pathlib import Path
import hashlib,json,sys,subprocess,datetime
D=Path(__file__).resolve().parent;ex=['manifest.json','final-verification-receipt.json']
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in ex:
  b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':ex,'files':files},indent=2)+'\n')
if '--final' in sys.argv:
 r=subprocess.run([sys.executable,'-B',str(D/'verify.py')],capture_output=True,text=True);assert r.returncode==0,r.stderr
 b=(D/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':r.returncode,'verification':json.loads(r.stdout),'negative_tests':json.loads((D/'negative-tests.json').read_text()),'read_only_verifier':True}
 (D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt))
