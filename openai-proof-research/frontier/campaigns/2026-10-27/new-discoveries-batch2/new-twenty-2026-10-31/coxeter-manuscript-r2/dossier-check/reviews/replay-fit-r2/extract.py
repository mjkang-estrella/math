from pathlib import Path,PurePosixPath
import sys,zipfile,stat
L=Path(__file__).resolve().parent
name=sys.argv[1]
assert name and all(c.isalnum() or c=='-' for c in name)
D=L/name;assert not D.exists();D.mkdir()
with zipfile.ZipFile(L/'330264-replay-fit-r2-source.zip') as z:
 for i in z.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and len(p.parts)==1 and p.suffix=='.lean'
  assert not stat.S_ISLNK(i.external_attr>>16)
  (D/p).write_bytes(z.read(i))
