from pathlib import Path
import zipfile,hashlib
p=Path(__file__).resolve().parent.parent
z=p.parent/'grid-formal-r3/grid-formal-r3-source.zip'
assert hashlib.sha256(z.read_bytes()).hexdigest()=='42498b10fb28faf228a1ac4ba7a509dbcd850c38caa47b03f359c2c566fa2030'
with zipfile.ZipFile(z) as f:
 for n in f.namelist():
  assert not n.startswith('/') and '..' not in Path(n).parts
  if n.startswith(('src/','controls/')): f.extract(n,p)
files=sorted((p/'src').glob('*.lean'))
assert len(files)==23
(p/'frozen-before.sha256').write_text(''.join(hashlib.sha256(f.read_bytes()).hexdigest()+'  src/'+f.name+'\n' for f in files))
