import zipfile,json,hashlib,sys
from pathlib import Path
R=Path(__file__).resolve().parent
with zipfile.ZipFile(R/'packet.zip') as z:
 names=z.namelist();assert len(names)==len(set(names))
 assert all(not Path(n).is_absolute() and '..' not in Path(n).parts for n in names)
 assert not any(n.endswith(('.olean','.olean.private','.olean.server','.ilean','.ir','.ir.sig','.o','.so','.pyc')) for n in names)
 dest=R/(sys.argv[1] if len(sys.argv)>1 else 'extracted-source')
 assert not dest.exists();z.extractall(dest)
print('Fresh packet extracted; no own compiled artifacts')
