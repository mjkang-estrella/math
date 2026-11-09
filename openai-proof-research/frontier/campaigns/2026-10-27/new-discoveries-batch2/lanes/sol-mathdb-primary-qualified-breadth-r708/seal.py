from pathlib import Path
import hashlib,json,datetime,subprocess,os
O=Path(__file__).resolve().parent
# Include every payload, including the verifier and this sealer.
excluded=['manifest.json','final-verification-receipt.json']
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in excluded:
  d=p.read_bytes();files.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(d).hexdigest(),'size':len(d)})
m=O/'manifest.json';m.write_text(json.dumps({'excluded_exact_paths':excluded,'files':files},indent=2)+'\n')
# Placeholder exists solely because exact payload verification expects the named receipt.
r=O/'final-verification-receipt.json';d=m.read_bytes();anchor={'sha256':hashlib.sha256(d).hexdigest(),'size':len(d)}
r.write_text(json.dumps({'manifest':anchor,'state':'pending'})+'\n')
guard=O.parent/'sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py'
p=subprocess.run(['python3','-B',str(guard),'python3','-B',str(O/'verify.py'),'--self-test'],capture_output=True,text=True)
assert p.returncode==0,p.stdout+p.stderr
result=json.loads(p.stdout)
r.write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'manifest':anchor,'verification':result,'guard':p.stderr.strip(),'limits':'512MiB AS/groupRSS CPU210s wall230s unchanged','mathematics_and_novelty':'HOLD / no credit; integrity is not scientific PASS'},indent=2)+'\n')
print(r.read_text())
