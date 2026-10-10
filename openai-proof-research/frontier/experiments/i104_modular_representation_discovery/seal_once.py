"""Preparation-only one-time seal, AFTER successful read-only preseal validation.
Refuses an existing seal. Never imported or invoked by verify.py.
"""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=Path('frontier/sources/i104_modular_representation_discovery')
E=Path('frontier/experiments/i104_modular_representation_discovery')
REPORT=Path('frontier/iterations/i104-modular-representation-discovery.md')
seal=ROOT/S/'seal.json';sealhash=ROOT/S/'seal.sha256'
assert not seal.exists() and not sealhash.exists(),'No resealing'
validation=json.loads((ROOT/S/'validation-before-seal.json').read_text())
assert validation['status']=='PASS' and validation['mode']=='preseal'
paths=[REPORT]
for base in [S,E]:
 for p in (ROOT/base).rglob('*'):
  assert not p.is_symlink()
  if p.is_file():paths.append(p.relative_to(ROOT))
files={str(p):hashlib.sha256((ROOT/p).read_bytes()).hexdigest() for p in sorted(paths)}
inventory=sorted(list(files)+[str(S/'seal.json'),str(S/'seal.sha256')])
obj={'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','owned_inventory':inventory,'files':files,'drift_allowed_live_only':['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],'limitations':'A digest replay is not proof certification.'}
raw=(json.dumps(obj,indent=2,sort_keys=True)+'\n').encode()
with seal.open('xb') as f:f.write(raw)
with sealhash.open('x') as f:f.write(hashlib.sha256(raw).hexdigest()+'\n')
print(json.dumps({'sealed_files':len(files),'owned_inventory':len(inventory),'seal_sha256':hashlib.sha256(raw).hexdigest()}))
