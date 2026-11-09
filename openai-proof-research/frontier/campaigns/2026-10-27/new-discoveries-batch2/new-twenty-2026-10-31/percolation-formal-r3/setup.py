from pathlib import Path
import zipfile, hashlib,json
root=Path(__file__).resolve().parent
z=root.parent/'percolation-formal-r2/source-only.zip'
with zipfile.ZipFile(z) as f:
 for n in f.namelist():
  p=Path(n)
  assert not p.is_absolute() and '..' not in p.parts
  if n.startswith('src/') or n=='module-order.txt':
   out=root/'packet'/n;out.parent.mkdir(parents=True,exist_ok=True);out.write_bytes(f.read(n))
(root/'results.json').write_text(json.dumps({'status':'in progress','inherited_zip_sha256':hashlib.sha256(z.read_bytes()).hexdigest(),'replay_pilot':{'additions':0,'status':'not yet measured'}},indent=2))
