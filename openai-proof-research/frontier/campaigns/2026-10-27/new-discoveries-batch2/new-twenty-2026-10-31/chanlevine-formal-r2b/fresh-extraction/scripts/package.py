from pathlib import Path
import zipfile,hashlib,json
r=Path(__file__).resolve().parent.parent
paths=sorted(list((r/'formal').glob('*.lean'))+list((r/'scripts').glob('*.py'))+[r/x for x in ['SUMMARY.md','REPRODUCE.md','frozen-before.json']])
z=r/'chanlevine-round2b-source.zip'
with zipfile.ZipFile(z,'w',zipfile.ZIP_DEFLATED) as a:
 for p in paths:
  name=p.relative_to(r).as_posix()
  assert not name.startswith('/') and '..' not in Path(name).parts
  a.write(p,name)
f=r/'fresh-extraction'
f.mkdir(exist_ok=False)
with zipfile.ZipFile(z) as a:
 for i in a.infolist():
  assert not i.filename.startswith('/') and '..' not in Path(i.filename).parts
 a.extractall(f)
for p in paths: assert p.read_bytes()==(f/p.relative_to(r)).read_bytes()
print(hashlib.sha256(z.read_bytes()).hexdigest(),len(paths),'safe source files; extraction matches')
