"""One-time development seal creation after a successful read-only preseal run.
This helper is not imported by the verifier. Exclusive creation forbids resealing.
"""
from pathlib import Path
import sys,hashlib,json,datetime
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i134_discrete_geometric_optimization'
E='frontier/experiments/i134_discrete_geometric_optimization'
REPORT='frontier/iterations/i134-discrete-geometric-optimization.md'
seal=ROOT/S/'seal.json';assert not seal.exists(),'no reseal'
assert len(sys.argv)==2,'supply successful preseal validated_inventory_sha256'
paths={REPORT}
for base in (S,E):
 for p in (ROOT/base).rglob('*'):
  assert not p.is_symlink()
  if p.is_file():paths.add(str(p.relative_to(ROOT)))
rows=[]
for p in sorted(paths):
 b=(ROOT/p).read_bytes();rows.append({'path':p,'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
h=hashlib.sha256(json.dumps(rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
assert h==sys.argv[1],'inventory changed since preseal validation'
x={'schema':'i134-exact-owned-v1','pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','roots':[REPORT,S+'/',E+'/'],'created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'validated_inventory_sha256':h,'files':rows,'scope':'inventory envelope, not signature/self-hash or mathematical certification'}
with seal.open('x') as f:f.write(json.dumps(x,indent=2,sort_keys=True)+'\n')
print(json.dumps({'seal_sha256':hashlib.sha256(seal.read_bytes()).hexdigest(),'files':len(rows),'validated_inventory_sha256':h}))
