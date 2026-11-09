from pathlib import Path
import json,hashlib,subprocess,sys
L=Path(__file__).resolve().parents[1]
# Deliberate negative tests: both must return nonzero without changing evidence.
log=[]
for arg in ['--test-bad-hash','--test-bad-set']:
 r=subprocess.run([sys.executable,'-B',str(L/'verify.py'),arg],capture_output=True,text=True)
 assert r.returncode!=0
 log.append({'case':arg,'exit':r.returncode,'stderr':r.stderr})
(L/'verifier-negative-tests.json').write_text(json.dumps(log,indent=2)+'\n')
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.relative_to(L).as_posix() not in {'manifest.json','verification-receipt.json'}:
  b=p.read_bytes();rows.append({'path':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(L/'manifest.json').write_text(json.dumps({'files':rows},indent=2)+'\n')
print('SEALED',len(rows),'files; two negative tests detected corruption')
