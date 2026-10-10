"""Author-only single seal after a successful read-only preseal validation."""
from pathlib import Path
import json,hashlib,datetime
S=Path('frontier/sources/i144_critical_siphon_window_repulsion');X=Path('frontier/experiments/i144_critical_siphon_window_repulsion')
seal=S/'seal.json';receipt=S/'preseal-validation.json';report=Path('frontier/iterations/i144-critical-siphon-window-repulsion.md')
assert not seal.exists(),'No resealing'
def row(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
files=[report];dirs=[]
for root in (S,X):
 dirs.append(str(root))
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():files.append(p)
  elif p.is_dir():dirs.append(str(p))
  else:raise AssertionError(str(p))
rows=[row(p) for p in sorted(files,key=str)];z=json.loads(receipt.read_bytes())
assert z['status']=='PASS' and z['mode']=='preseal-read-only'
assert z['validated_files']==[r for r in rows if r['path']!=str(receipt)]
assert z['all_immutable_checks_before_diagnostics'] and z['corpus_traversals']==1
out=dict(schema='i144-one-final-seal-v1',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),policy='One final seal after successful validation. No reseal or repair. All owned bytes except seal itself are inventoried; only four original live ledgers may drift.',directories=sorted(dirs),files=rows)
with seal.open('x') as f:f.write(json.dumps(out,indent=2)+'\n')
print(hashlib.sha256(seal.read_bytes()).hexdigest())
