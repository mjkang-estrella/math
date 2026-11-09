"""Read-only verify the input hashes and archive safety; print current pins.
No extraction/build occurs in this helper. See build.py and check.py for replay.
"""
from pathlib import Path,PurePosixPath
import hashlib,json,zipfile
D=Path(__file__).resolve().parents[1];S=D.parent/'expanded-corpus-r126'
current={str(p.relative_to(S)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(S.rglob('*')) if p.is_file()}
assert current==json.loads((D/'inputs-before.json').read_text())==json.loads((D/'inputs-after.json').read_text())
z=S/'338258-proof-source.zip';assert hashlib.sha256(z.read_bytes()).hexdigest()=='628b850b31e347ab2d395fa6c11474c4ea8765c1cbdb6cc051e1ed3d77b0d198'
with zipfile.ZipFile(z) as archive:
 for i in archive.infolist():
  p=PurePosixPath(i.filename)
  assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
  assert ((i.external_attr>>16)&0o170000)!=0o120000
print('PASS: all',len(current),'input files unchanged; archive paths safe')
