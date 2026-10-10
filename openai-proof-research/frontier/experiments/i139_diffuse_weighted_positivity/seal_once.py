"""Preparation-only unique final seal. Never imported by offline verifier."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i139_diffuse_weighted_positivity';E=R/'frontier/experiments/i139_diffuse_weighted_positivity'
p=S/'seal.json';assert not p.exists(),'No resealing'
v=json.loads((E/'validation.json').read_text());assert v['status']=='PASS' and v['exit_code']==0
inv=json.loads((S/'inventory.json').read_text());paths=inv['owned_paths'];assert paths==sorted(set(paths))
actual={str(x.relative_to(R)) for base in [S,E] for x in base.rglob('*') if x.is_file()}|{'frontier/iterations/i139-diffuse-weighted-positivity.md'}
assert actual==set(paths)
for x,h in v['validated_sha256'].items():assert hashlib.sha256((R/x).read_bytes()).hexdigest()==h,('changed after validation',x)
assert set(v['validated_sha256'])==set(paths)-{str((E/'validation.json').relative_to(R))}
body=dict(sha256={x:hashlib.sha256((R/x).read_bytes()).hexdigest() for x in paths},scope='One final seal after read-only preseal validation; evidence and finite instances only')
with p.open('x') as f:json.dump(body,f,indent=2);f.write('\n')
print(hashlib.sha256(p.read_bytes()).hexdigest())
