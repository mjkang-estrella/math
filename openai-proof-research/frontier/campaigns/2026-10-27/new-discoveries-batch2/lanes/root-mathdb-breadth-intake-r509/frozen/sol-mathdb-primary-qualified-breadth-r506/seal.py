from pathlib import Path
import hashlib,json,subprocess,sys,datetime
O=Path(__file__).resolve().parent;L=O.parent
b=json.loads((O/'flat-bindings.json').read_text())
for p in [L/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py',L.parent/'AGENTS.md',L.parents[4]/'AGENTS.md']:
 data=p.read_bytes()
 if str(p) not in {e['path'] for e in b}:b.append({'path':str(p),'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
(O/'flat-bindings.json').write_text(json.dumps(b,indent=2)+'\n')
exc=['manifest.json','final-verification-receipt.json'];files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in exc:
  data=p.read_bytes();files.append({'path':str(p.relative_to(O)),'size':len(data),'sha256':hashlib.sha256(data).hexdigest()})
(O/'manifest.json').write_text(json.dumps({'excluded_exact_paths':exc,'files':files},indent=2)+'\n')
p=subprocess.run([sys.executable,'-B',str(O/'verify.py'),'--negative-tests'],capture_output=True,text=True)
data=(O/'manifest.json').read_bytes();receipt={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest_sha256':hashlib.sha256(data).hexdigest(),'manifest_size':len(data),'verifier_exit':p.returncode,'stdout':p.stdout,'stderr':p.stderr,'integrity_only':True}
(O/'final-verification-receipt.json').write_text(json.dumps(receipt,indent=2)+'\n');print(json.dumps(receipt));sys.exit(p.returncode)
