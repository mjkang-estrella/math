from pathlib import Path
import zipfile,hashlib,json
L=Path(__file__).resolve().parent
manifest=json.loads((L/'merge-manifest.json').read_text())
for n,r in manifest['union'].items():assert hashlib.sha256((L/'merged'/n).read_bytes()).hexdigest()==r['sha256']
files={str(p.relative_to(L/'merged')):p for p in (L/'merged').rglob('*.lean')}
for p in (L/'scripts').glob('*'):
 if p.suffix in ['.py','.lean']: files['scripts/'+p.name]=p
files['module-order.json']=L/'module-order.json'
with zipfile.ZipFile(L/'ulas-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for name,p in sorted(files.items()):
  assert not Path(name).is_absolute() and '..' not in Path(name).parts
  z.writestr(name,p.read_bytes())
fresh=L/'fresh-replay';assert not fresh.exists();fresh.mkdir()
with zipfile.ZipFile(L/'ulas-source.zip') as z:
 z.extractall(fresh)
 for n,p in files.items():assert (fresh/n).read_bytes()==p.read_bytes()
print('zip sha256',hashlib.sha256((L/'ulas-source.zip').read_bytes()).hexdigest(),'entries',len(files))
