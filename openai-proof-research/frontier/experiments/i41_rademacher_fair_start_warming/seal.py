"""ONE-TIME seal creation. Refuses to refresh an existing seal."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i41_rademacher_fair_start_warming'
E=R/'frontier/experiments/i41_rademacher_fair_start_warming'
target=S/'artifact-seal.json'
assert not target.exists(),'Never refresh a sealed artifact set.'
paths=[R/'frontier/iterations/i41-rademacher-fair-start-warming.md']+list(S.rglob('*'))+list(E.rglob('*'))
files={}
for p in sorted(paths):
 if not p.is_file() or p==target:continue
 b=p.read_bytes();files[str(p.relative_to(R))]={'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()}
with target.open('x') as f:json.dump({'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','scope':'I41 report and evidence only. Existing dependency seals are never refreshed.','files':files},f,indent=2);f.write('\n')
print(json.dumps({'sealed_files':len(files),'seal':str(target.relative_to(R))}))
