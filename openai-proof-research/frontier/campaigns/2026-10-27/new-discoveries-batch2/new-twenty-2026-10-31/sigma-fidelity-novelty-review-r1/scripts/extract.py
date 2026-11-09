"""Independent safe extraction; invoke with a new destination inside this lane."""
from pathlib import Path
import zipfile,sys,hashlib,json
R=Path(__file__).resolve().parents[1]
dest=R/sys.argv[1]
assert dest.parent==R and not dest.exists()
z=zipfile.ZipFile(R.parent/'sigma-formal-r2/proof-packet.zip')
names=set(); total=0
for i in z.infolist():
 p=Path(i.filename); mode=i.external_attr>>16
 assert not p.is_absolute() and '..' not in p.parts and '\\' not in i.filename
 assert i.filename not in names and mode&0o170000!=0o120000
 assert p.suffix not in ['.olean','.ilean','.so'] and i.file_size<20000000
 names.add(i.filename);total+=i.file_size
assert total<100000000
dest.mkdir();z.extractall(dest)
for name,h in json.loads((dest/'MANIFEST.json').read_text())['files'].items():
 assert hashlib.sha256((dest/name).read_bytes()).hexdigest()==h
print('safe extraction and manifest verified',len(names),total)
