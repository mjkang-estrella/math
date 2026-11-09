from pathlib import Path
import json,hashlib,subprocess,sys,datetime
P=Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
def seal():
 files=[]
 for p in sorted(P.rglob('*')):
  n=str(p.relative_to(P))
  if p.is_file() and n not in excluded:
   b=p.read_bytes();files.append({'path':n,'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
 (P/'manifest.json').write_text(json.dumps({'excluded_exact_paths':excluded,'files':files},indent=2)+'\n')
seal();results=[]
for mode in ['--negative-hash','--negative-size','--negative-extra']:
 p=subprocess.run([sys.executable,'-B',str(P/'verify.py'),mode],capture_output=True,text=True,timeout=30)
 assert p.returncode!=0,mode
 results.append({'mode':mode,'exit':p.returncode,'stderr':p.stderr,'method':'in-memory altered expected hash/size or virtual extra file; originals untouched'})
(P/'negative-test-results.json').write_text(json.dumps(results,indent=2)+'\n');seal()
p=subprocess.run([sys.executable,'-B',str(P/'verify.py')],capture_output=True,text=True,timeout=60)
assert p.returncode==0,p.stderr
r=json.loads(p.stdout);r.update(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),negative_rejection_tests=3,verifier_exit=0,read_only_verifier=True)
(P/'final-verification-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps(r))
