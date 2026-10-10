"""One final seal only, after successful read-only preseal validation."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i133_fixed_metric_harmonic_growth'
E=ROOT/'frontier/experiments/i133_fixed_metric_harmonic_growth'
sha=lambda b:hashlib.sha256(b).hexdigest()
seal=S/'seal.json'
assert not seal.exists(),'No repair or reseal permitted'
inventory=json.loads((S/'inventory.json').read_text())
paths=inventory['owned_paths']
assert paths==sorted(set(paths))
validation=json.loads((E/'validation.json').read_text())
assert validation['status']=='PASS' and validation['exit_code']==0
assert validation['command']==['python3','-B','frontier/experiments/i133_fixed_metric_harmonic_growth/verify.py','--preseal']
expected=set(paths)-{'frontier/experiments/i133_fixed_metric_harmonic_growth/validation.json'}
assert set(validation['preseal_owned_sha256'])==expected
for p,h in validation['preseal_owned_sha256'].items():
    assert sha((ROOT/p).read_bytes())==h,('changed since validation',p)
actual={str(p.relative_to(ROOT)) for d in (S,E) for p in d.rglob('*') if p.is_file()}
actual.add('frontier/iterations/i133-fixed-metric-harmonic-growth.md')
assert actual==set(paths)
for d in (S,E):
    assert not any(p.is_symlink() for p in d.rglob('*'))
seal.write_text(json.dumps(dict(schema=1,scope='I133 exact owned immutable inventory; evidence only',
    sha256={p:sha((ROOT/p).read_bytes()) for p in paths}),indent=2)+'\n')
print(sha(seal.read_bytes()))
