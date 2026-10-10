"""Create I40's seal ONCE. Refuses replacement; never run on dependencies."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i40_critical_sk_waiting_relaxation'
E=R/'frontier/experiments/i40_critical_sk_waiting_relaxation'
seal=S/'artifact-seal.json'
assert not seal.exists(),'A seal exists. Do not refresh it.'
ps=[R/'frontier/iterations/i40-critical-sk-waiting-relaxation.md']+list(S.rglob('*'))+list(E.rglob('*'))
files={}
for p in sorted(ps):
 if p.is_file():
  b=p.read_bytes();files[str(p.relative_to(R))]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
with seal.open('x') as f:
 json.dump({'format':'I40 one-time SHA-256 artifact seal v1','note':'Every I40 owned artifact except this seal. Read-only verifier. Dependencies never refreshed. Live ledger drift is separate.','files':files},f,indent=2);f.write('\n')
print(json.dumps({'sealed_artifacts':len(files),'seal_sha256':hashlib.sha256(seal.read_bytes()).hexdigest()}))
