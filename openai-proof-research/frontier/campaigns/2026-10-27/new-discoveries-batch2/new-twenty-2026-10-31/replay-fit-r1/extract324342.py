from pathlib import Path,PurePosixPath
import zipfile,stat,sys,hashlib
L=Path(__file__).resolve().parent
d=(L/sys.argv[1]).resolve();assert d.is_relative_to(L) and not d.exists()
z=L/'324342-replay-fit-source.zip'
assert hashlib.sha256(z.read_bytes()).hexdigest()==(L/'324342-packet.sha256').read_text().split()[0]
with zipfile.ZipFile(z) as a:
 for i in a.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16) and p.suffix=='.lean'
  dst=d/p;dst.parent.mkdir(parents=True,exist_ok=True);dst.write_bytes(a.read(i))
