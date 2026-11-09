from pathlib import Path
import json,hashlib,subprocess,os,datetime
O=Path(__file__).resolve().parent
excluded=['manifest.json','final-verification-receipt.json']
def entry(p):
 b=p.read_bytes();return {'path':str(p.relative_to(O)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()}
def seal():
 m={'excluded_exact_paths':excluded,'files':[entry(p) for p in sorted(O.rglob('*')) if p.is_file() and str(p.relative_to(O)) not in excluded]};(O/'manifest.json').write_text(json.dumps(m,indent=2)+'\n')
seal()
results=[]
for flag in ['--negative-hash','--negative-size','--negative-extra']:
 # Already in the fixed guard's process group and resource envelope.
 p=subprocess.run(['python3','-B',str(O/'verify.py'),flag],capture_output=True,text=True)
 assert p.returncode!=0,(flag,p.stdout,p.stderr)
 results.append({'test':flag,'exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'method':'in-memory same validator; originals unchanged'})
(O/'negative-test-results.json').write_text(json.dumps(results,indent=2)+'\n');seal()
p=subprocess.run(['python3','-B',str(O/'verify.py')],capture_output=True,text=True);assert p.returncode==0,(p.stdout,p.stderr)
e=entry(O/'manifest.json');(O/'final-verification-receipt.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':e,'verification_exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'negative_tests':3,'integrity_only':True},indent=2)+'\n')
print(json.dumps({'manifest':e,'verification':p.stdout,'negative_tests':results},indent=2))
