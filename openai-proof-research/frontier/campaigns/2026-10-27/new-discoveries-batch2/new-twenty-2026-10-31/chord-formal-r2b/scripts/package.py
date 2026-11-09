from pathlib import Path
import zipfile,hashlib,json
R=Path(__file__).resolve().parent.parent
files=[R/'modules.txt',R/'inherited-modules.txt',R/'certificate.json',R/'regression.json']+list((R/'src').glob('*.lean'))+list((R/'scripts').glob('*'))+list(R.glob('*.md'))+list((R/'hashes').glob('*'))
with zipfile.ZipFile(R/'chord-comb2-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files):
  if p.is_file():z.write(p,p.relative_to(R).as_posix())
fresh=R/'fresh-extraction'
fresh.mkdir(exist_ok=False)
with zipfile.ZipFile(R/'chord-comb2-source.zip') as z:
 for info in z.infolist():
  p=Path(info.filename)
  assert not p.is_absolute() and '..' not in p.parts
 z.extractall(fresh)
 for info in z.infolist():
  (fresh/info.filename).chmod((info.external_attr >> 16) & 0o777)
for d in ('logs','tmp','cache','build'):(fresh/d).mkdir()
print('archive',hashlib.sha256((R/'chord-comb2-source.zip').read_bytes()).hexdigest(),'fresh',fresh)
