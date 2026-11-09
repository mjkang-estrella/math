from pathlib import Path
import zipfile,hashlib,json,shutil
r=Path(__file__).resolve().parent; old=r.parent/'percolation-formal-r7'
def copy(a,b):
 shutil.copyfile(a,b); assert hashlib.sha256(a.read_bytes()).digest()==hashlib.sha256(b.read_bytes()).digest()
copy(old/'source-only.zip',r/'r7-source.zip')
assert hashlib.sha256((r/'r7-source.zip').read_bytes()).hexdigest()=='932f1d739121ffe164a9f75148eaab45a2049949a5158d6385eedb7892883f52'
p=r/'packet';p.mkdir(exist_ok=True)
with zipfile.ZipFile(r/'r7-source.zip') as z:
 for n in z.namelist():
  a=Path(n);assert not a.is_absolute() and '..' not in a.parts
 z.extractall(p)
for n in ['normalized.cnf','normalized-trimmed.json']:copy(r.parent/'percolation-formal-r3'/n,r/n)
copy(old/'inherited.zip',r/'inherited.zip')
# The historical sources provide proof bodies as data; never execute their scripts.
with zipfile.ZipFile(r/'inherited.zip') as z:
 for n in z.namelist():
  a=Path(n);assert not a.is_absolute() and '..' not in a.parts
 z.extractall(r/'historical')
(r/'retained-source-comparison.json').write_text(json.dumps({n:hashlib.sha256((p/n).read_bytes()).hexdigest() for n in zipfile.ZipFile(r/'r7-source.zip').namelist() if n.endswith('.lean')},indent=2))
