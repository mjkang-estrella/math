import pathlib,zipfile,hashlib
r=pathlib.Path(__file__).resolve().parent
for archive,dest in [('r6-source.zip','packet'),('inherited.zip','inherited')]:
 with zipfile.ZipFile(r/archive) as z:
  for n in z.namelist():
   p=pathlib.PurePosixPath(n)
   assert not p.is_absolute() and '..' not in p.parts
  z.extractall(r/dest)
for name in ['normalized.cnf','normalized-trimmed.json']:
 src=r.parent/'percolation-formal-r3'/name
 data=src.read_bytes();(r/name).write_bytes(data)
 assert hashlib.sha256(data).digest()==hashlib.sha256((r/name).read_bytes()).digest()
 print(name,hashlib.sha256(data).hexdigest())
