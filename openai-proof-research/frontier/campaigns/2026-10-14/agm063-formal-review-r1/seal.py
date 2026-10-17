"""Seal an already completed review; no mathematical verification. MIT."""
import hashlib,json
from pathlib import Path
PIN='ca6bdb0cccd691d0c8a94ff8ec3bfbd9ccdd87a64ba5b4cf344a1b1c73b8ad9c'
def seal(root):
 files=[];dirs=[]
 for p in sorted(root.rglob('*')):
  assert not p.is_symlink()
  n=p.relative_to(root).as_posix()
  if p.is_dir():dirs.append(n)
  elif n!='review-manifest.json':
   b=p.read_bytes();files.append(dict(path=n,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
 m=dict(schema='AGM063-independent-formal-review-r1',verdict='PASS_SCOPED_SUPPORT',full_theorem_formalized=False,implementation_anchor=PIN,files=files,directories=dirs)
 raw=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode();(root/'review-manifest.json').write_bytes(raw)
 return hashlib.sha256(raw).hexdigest()
if __name__=='__main__':print(seal(Path(__file__).resolve().parent))
