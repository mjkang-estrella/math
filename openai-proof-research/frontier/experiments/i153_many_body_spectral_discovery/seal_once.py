"""Author-only single seal. Requires completed read-only prevalidation; no reseal."""
from pathlib import Path
import json,hashlib
S=Path('frontier/sources/i153_many_body_spectral_discovery');X=Path('frontier/experiments/i153_many_body_spectral_discovery');R=Path('frontier/iterations/i153-many-body-spectral-discovery.md')
p=S/'seal.json';assert not p.exists()
receipt=json.loads((S/'preseal-validation.json').read_text());assert receipt['status']=='PASS' and receipt['mode']=='preseal-read-only'
files=[R];dirs=[]
for root in (S,X):
 dirs.append(str(root))
 for f in root.rglob('*'):
  assert not f.is_symlink()
  if f.is_file():files.append(f)
  elif f.is_dir():dirs.append(str(f))
rows=[]
for f in sorted(files,key=str):
 b=f.read_bytes();rows.append(dict(path=str(f),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
assert [r for r in rows if r['path']!=str(S/'preseal-validation.json')]==receipt['validated_files']
with p.open('x') as f:json.dump(dict(files=rows,directories=sorted(dirs),scope='Single immutable evidence seal; no mathematical certification'),f,indent=2);f.write('\n')
print(json.dumps(dict(seal=str(p),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),files=len(rows))))
