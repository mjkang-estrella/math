"""One author seal, only after successful unchanged prevalidation; no repair mode."""
from pathlib import Path
import json,hashlib
S=Path('frontier/sources/i155_fixed_sector_bfss_counting');X=Path('frontier/experiments/i155_fixed_sector_bfss_counting')
report=Path('frontier/iterations/i155-fixed-sector-bfss-counting.md');seal=S/'seal.json';receipt=S/'preseal-validation.json'
assert not seal.exists()
def row(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
fs=[report];ds=[]
for root in (S,X):
 ds.append(str(root))
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():fs.append(p)
  elif p.is_dir():ds.append(str(p))
rows=sorted((row(p) for p in fs),key=lambda r:r['path']);v=json.loads(receipt.read_text())
assert v['status']=='PASS' and v['mode']=='preseal-read-only'
assert [r for r in rows if r['path']!=str(receipt)]==v['validated_files']
with seal.open('x') as f:json.dump(dict(files=rows,directories=sorted(ds),scope='Single immutable evidence seal; not mathematical or contribution certification.'),f,indent=2);f.write('\n')
print(json.dumps(dict(seal=str(seal),sha256=hashlib.sha256(seal.read_bytes()).hexdigest(),files=len(rows),directories=len(ds))))
