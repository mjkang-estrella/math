from pathlib import Path,PurePosixPath
import zipfile,stat,hashlib,json
L=Path(__file__).resolve().parent
old=(L/'original-324342/ConferenceMDS324342.lean').read_bytes()
new=(L/'narrow-324342/ConferenceMDS324342.lean').read_bytes()
assert new[new.index(b'\n\n'):]==old[old.index(b'\n\n'):]
with zipfile.ZipFile(L/'324342-replay-fit-source.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted((L/'narrow-324342').glob('*.lean')):z.writestr(p.name,p.read_bytes())
with zipfile.ZipFile(L/'324342-replay-fit-source.zip') as z:
 for i in z.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and not stat.S_ISLNK(i.external_attr>>16)
  assert i.filename.endswith('.lean')
  d=L/'fresh-324342'/p;d.parent.mkdir(exist_ok=True,parents=True);assert not d.exists();d.write_bytes(z.read(i))
(L/'324342-packet.sha256').write_text(hashlib.sha256((L/'324342-replay-fit-source.zip').read_bytes()).hexdigest()+'  324342-replay-fit-source.zip\n')
