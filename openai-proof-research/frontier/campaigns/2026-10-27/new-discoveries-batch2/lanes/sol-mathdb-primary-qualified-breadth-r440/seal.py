from pathlib import Path
import hashlib,json,subprocess,sys,datetime
R=Path(__file__).resolve().parent
sha=lambda b:hashlib.sha256(b).hexdigest()
es=[]
for p in sorted(R.rglob('*')):
 if p.is_file() and str(p.relative_to(R)) not in {'manifest.json','final-receipt.json'}:
  b=p.read_bytes();es.append({'path':str(p.relative_to(R)),'size':len(b),'sha256':sha(b)})
m={'files':es,'excluded_exact_relative_paths':['manifest.json','final-receipt.json'],'canonicalization':'json.dumps(record,sort_keys=True,ensure_ascii=False,separators=(comma,colon)).encode(UTF-8)'}
(R/'manifest.json').write_text(json.dumps(m,indent=2,sort_keys=True)+'\n')
g=R.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
p=subprocess.run([sys.executable,str(g),sys.executable,'-B',str(R/'verify.py')],capture_output=True,text=True)
receipt={'verified_at_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':sha((R/'manifest.json').read_bytes()),'verifier_exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'status':'PASS' if p.returncode==0 else 'FAIL'}
(R/'final-receipt.json').write_text(json.dumps(receipt,indent=2,sort_keys=True)+'\n');print(json.dumps(receipt,indent=2));sys.exit(p.returncode)
