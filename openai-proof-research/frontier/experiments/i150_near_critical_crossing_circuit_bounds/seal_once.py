"""Author-only single seal. Requires successful read-only prevalidation of exact bytes."""
from pathlib import Path
import json,hashlib
S=Path('frontier/sources/i150_near_critical_crossing_circuit_bounds');E=Path('frontier/experiments/i150_near_critical_crossing_circuit_bounds');R=Path('frontier/iterations/i150-near-critical-crossing-circuit-bounds.md')
seal=S/'seal.json';receipt=S/'preseal-validation.json'
assert not seal.exists(),'one seal only; no reseal'
v=json.loads(receipt.read_bytes());assert v['status']=='PASS' and v['mode']=='preseal-read-only'
def row(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
files=[R];dirs=[]
for root in (S,E):
 dirs.append(str(root))
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():files.append(p)
  elif p.is_dir():dirs.append(str(p))
rows=sorted([row(p) for p in files],key=lambda r:r['path'])
assert [r for r in rows if r['path']!=str(receipt)]==v['validated_files'],'bytes changed after prevalidation'
z=dict(format='I150 one-shot exact inventory',files=rows,directories=sorted(dirs),scope='Immutable integrity and finite calculations, not universal-proof or contribution certification')
with seal.open('x') as f:json.dump(z,f,ensure_ascii=False,indent=2);f.write('\n')
print(json.dumps(dict(seal=str(seal),sha256=hashlib.sha256(seal.read_bytes()).hexdigest(),files=len(rows),directories=len(dirs))))
