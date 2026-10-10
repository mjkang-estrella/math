"""One-shot acquisition-side seal creation, never called by offline replay."""
import json,hashlib
from pathlib import Path
S=Path('frontier/sources/i132_discrete_probability_discovery');X=Path('frontier/experiments/i132_discrete_probability_discovery');R=Path('frontier/iterations/i132-discrete-probability-discovery.md')
assert not (S/'seal.json').exists(),'No repair/reseal'
def row(p):
 b=Path(p).read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
files=[str(R)];dirs=[]
for root in (S,X):
 assert root.is_dir() and not root.is_symlink();dirs.append(str(root))
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_dir():dirs.append(str(p))
  elif p.is_file():files.append(str(p))
  else:raise AssertionError('Unexpected object')
assert len(files)==len(set(files)) and len(dirs)==len(set(dirs))
files=sorted(files);dirs=sorted(dirs)
receipt=json.loads((S/'preseal-validation.json').read_text())
assert receipt['status']=='PASS' and receipt['mode']=='preseal-read-only'
assert receipt['all_immutable_checks_before_diagnostics'] is True and receipt['corpus_traversals']==1
assert receipt['validated_files']==[row(p) for p in files if p!=str(S/'preseal-validation.json')]
seal=dict(schema='i132-one-final-seal-v1',globally_sorted_exact_inventory=True,files=[row(p) for p in files],directories=dirs,pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',scope='Immutable evidence and finite diagnostics only; analytic and contribution claims remain scoped in report')
with (S/'seal.json').open('x') as f:json.dump(seal,f,indent=2);f.write('\n')
print(json.dumps(dict(seal_sha256=row(S/'seal.json')['sha256'],files=len(files),directories=len(dirs),globally_sorted_exact_inventory=True)))
