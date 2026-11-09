from pathlib import Path
import json,hashlib,subprocess,datetime
D=Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
def manifest():
 files=[]
 for p in sorted(D.rglob('*')):
  if p.is_file() and str(p.relative_to(D)) not in excluded:
   b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
 (D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':excluded,'files':files},indent=2)+'\n')
manifest();neg=[]
for kind in ['hash','size','extra-file']:
 p=subprocess.run(['bash',str(D/'verify.sh'),'--negative',kind],capture_output=True,text=True); assert p.returncode!=0
 neg.append({'kind':kind,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'method':'in-memory mutation of verifier manifest descriptor or observed file set; originals never mutated'})
(D/'negative-tests.json').write_text(json.dumps(neg,indent=2)+'\n');manifest()
p=subprocess.run(['bash',str(D/'verify.sh')],capture_output=True,text=True)
b=(D/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(b).hexdigest(),'manifest_size':len(b),'verifier_exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'negative_test_rejections':len(neg),'integrity_only':True,'mathematics_novelty':'HOLD / no acceptance'}
(D/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));assert p.returncode==0
