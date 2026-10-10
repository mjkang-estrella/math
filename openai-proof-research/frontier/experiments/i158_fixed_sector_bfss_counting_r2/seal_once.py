"""One author seal only, after successful read-only prevalidation. No resealing."""
from pathlib import Path
import json,hashlib
S=Path('frontier/sources/i158_fixed_sector_bfss_counting_r2');X=Path('frontier/experiments/i158_fixed_sector_bfss_counting_r2');R=Path('frontier/reviews/i158-fixed-sector-bfss-counting-r2.md')
seal=S/'seal.json';receipt=S/'preseal-validation.json';assert not seal.exists()
def row(p):
 b=p.read_bytes();return dict(path=str(p),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b))
files=[R];dirs=[]
for root in (S,X):
 dirs.append(str(root))
 for p in root.rglob('*'):
  assert not p.is_symlink()
  if p.is_dir():dirs.append(str(p))
  else:files.append(p)
files=sorted(files,key=str);rows=[row(p) for p in files if p!=receipt]
v=json.loads(receipt.read_text());assert v['status']=='PASS' and v['mode']=='preseal-read-only'
assert v['validated_files']==rows and v['owned_directories']==sorted(dirs)
assert v['new_diagnostics']=={'status':'not run before seal'} and v['complete_requested_review'] is False
with seal.open('x') as f:json.dump(dict(files=[row(p) for p in files],directories=sorted(dirs),scope='Immutable review package; full requested review remains unresolved.'),f,indent=2);f.write('\n')
print('Sealed once; no repair/reseal mode.')
