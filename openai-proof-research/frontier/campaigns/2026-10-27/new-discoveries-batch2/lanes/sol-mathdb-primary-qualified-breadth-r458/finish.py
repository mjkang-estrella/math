from pathlib import Path
import json,hashlib,datetime,subprocess,sys
L=Path(__file__).resolve().parent
h=lambda b:hashlib.sha256(b).hexdigest()
files=[{'path':str(p.relative_to(L)),'size':p.stat().st_size,'sha256':h(p.read_bytes())} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['manifest.json','final-receipt.json']]
(L/'manifest.json').write_text(json.dumps({'files':files,'scope':'exact lane payload excluding manifest and separate final receipt','counts_unchanged':'9 additional / 39 total / next 40'},indent=2)+'\n')
guard=L.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
r=subprocess.run(['python3','-B',str(guard),'python3','-B',str(L/'verify.py')],capture_output=True,text=True)
print(r.stdout,end='');print(r.stderr,end='',file=sys.stderr)
if r.returncode:sys.exit(r.returncode)
result=json.loads(r.stdout)
receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'integrity':'PASS','manifest_sha256':h((L/'manifest.json').read_bytes()),'verification':result,'verifier_guard_log':r.stderr,'source_proof_and_novelty_status':'NOT PASS; qualified statement screen only; 46 HOLD and four credit exclusions','root_acceptance':'not requested or granted','counts_unchanged':'9 additional / 39 total / next 40'}
(L/'final-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n')
