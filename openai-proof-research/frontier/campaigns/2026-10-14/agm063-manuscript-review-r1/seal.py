"""Seal a completed independent review; integrity inventory only. MIT."""
import hashlib,json
from pathlib import Path
MANUSCRIPT='5a043ad5acdf541b9a10d912dbd0339b3c8c0aa2650bd92a4a41d5422d0c34bb'
PDF='bb9d911bf972f91d57f6e00b037ecd012e2cd892927d22ebbb5fa8ca0682b4b5'
def seal(root):
 files=[];dirs=[]
 for p in sorted(root.rglob('*')):
  assert not p.is_symlink()
  n=p.relative_to(root).as_posix()
  if p.is_dir():dirs.append(n)
  elif n!='review-manifest.json':
   b=p.read_bytes();files.append(dict(path=n,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
 m=dict(schema='AGM063-independent-manuscript-review-r1',verdict='PASS_FULL_MANUSCRIPT_AGM063',full_theorem_formalized=False,manuscript_manifest_sha256=MANUSCRIPT,pdf_sha256=PDF,files=files,directories=dirs)
 raw=(json.dumps(m,indent=2,sort_keys=True)+'\n').encode();(root/'review-manifest.json').write_bytes(raw)
 return hashlib.sha256(raw).hexdigest()
if __name__=='__main__':print(seal(Path(__file__).resolve().parent))
