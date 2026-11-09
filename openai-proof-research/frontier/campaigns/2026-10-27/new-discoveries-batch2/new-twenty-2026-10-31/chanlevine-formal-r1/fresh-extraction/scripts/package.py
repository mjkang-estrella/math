from pathlib import Path
import hashlib, json, zipfile
r=Path(__file__).resolve().parent.parent
paths=sorted(list((r/'formal').glob('*.lean'))+list((r/'scripts').glob('*.py'))+list((r/'scripts').glob('*.sh'))+[r/f for f in ['PROOF.md','SUMMARY.md','REPRODUCE.md','STATEMENT-CORRESPONDENCE.md']])
archive=r/'chanlevine-round1-source.zip'
with zipfile.ZipFile(archive,'w',zipfile.ZIP_DEFLATED) as z:
 for p in paths:
  name=p.relative_to(r).as_posix()
  assert not name.startswith('/') and '..' not in Path(name).parts
  z.write(p,name)
fresh=r/'fresh-extraction'
fresh.mkdir(exist_ok=False)
with zipfile.ZipFile(archive) as z:
 for info in z.infolist():
  assert not info.filename.startswith('/') and '..' not in Path(info.filename).parts
 z.extractall(fresh)
for p in paths:
 assert hashlib.sha256(p.read_bytes()).digest()==hashlib.sha256((fresh/p.relative_to(r)).read_bytes()).digest()
print(archive,hashlib.sha256(archive.read_bytes()).hexdigest(),len(paths),'source files; extraction matches')
