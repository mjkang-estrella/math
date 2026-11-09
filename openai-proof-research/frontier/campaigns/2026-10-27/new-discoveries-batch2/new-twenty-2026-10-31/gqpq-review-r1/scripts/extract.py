"""Safely reproduce extraction into a new subdirectory of this review lane."""
from pathlib import Path
import zipfile,sys,hashlib,json
D=Path(__file__).resolve().parents[1]
dest=D/(sys.argv[1] if len(sys.argv)>1 else 'extracted-again')
assert dest.resolve().is_relative_to(D) and not dest.exists()
z=zipfile.ZipFile(D.parent/'expanded-corpus-r72/377831-proof-packet.zip')
for i in z.infolist():
 p=Path(i.filename)
 assert not p.is_absolute() and '..' not in p.parts
 assert (i.external_attr>>16)&0o170000!=0o120000
 assert i.file_size<1000000
z.extractall(dest)
manifest=json.loads((dest/'source-manifest.json').read_text())
for name,expected in manifest.items():assert hashlib.sha256((dest/name).read_bytes()).hexdigest()==expected
print(dest)
