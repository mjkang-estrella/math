"""Author-side one-time seal. Never called by replay."""
import hashlib,json
from pathlib import Path
S=Path('frontier/sources/i135_complex_analysis_discovery');X=Path('frontier/experiments/i135_complex_analysis_discovery');R=Path('frontier/iterations/i135-complex-analysis-discovery.md')
def row(p):b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
assert not (S/'seal.json').exists()
files=[R];dirs=[]
for base in (S,X):
 dirs.append(str(base))
 for p in base.rglob('*'):
  assert not p.is_symlink()
  if p.is_dir():dirs.append(str(p))
  elif p.is_file():files.append(p)
  else:raise AssertionError('Unexpected object')
files=sorted(files,key=str);dirs=sorted(dirs);assert len(files)==len(set(files)) and len(dirs)==len(set(dirs))
receipt=json.loads((S/'preseal-validation.json').read_text());assert receipt['status']=='PASS'
assert receipt['validated_files']==[row(p) for p in files if p!=S/'preseal-validation.json']
seal=dict(schema='i135-one-final-seal-v1',globally_sorted_exact_inventory=True,files=[row(p) for p in files],directories=dirs)
with (S/'seal.json').open('x') as f:f.write(json.dumps(seal,indent=2)+'\n')
print(hashlib.sha256((S/'seal.json').read_bytes()).hexdigest())
