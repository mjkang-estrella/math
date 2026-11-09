from pathlib import Path
import json,hashlib,sys,zipfile
R=Path.cwd()
for m in ['PAYLOAD-MANIFEST.json']:
 d=json.loads((R/m).read_text())
 for path,e in d['files'].items():
  b=(R/path).read_bytes(); assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],path
 print('PASS',m,len(d['files']),'files')
for p in sorted(R.glob('*.zip')):
 with zipfile.ZipFile(p) as z:
  assert z.testzip() is None
  if 'ARCHIVE-MANIFEST.json' in z.namelist():
   d=json.loads(z.read('ARCHIVE-MANIFEST.json'))
   assert set(z.namelist())==set(d['files'])|{'ARCHIVE-MANIFEST.json'}
   for path,e in d['files'].items():
    b=z.read(path); assert len(b)==e['bytes'] and hashlib.sha256(b).hexdigest()==e['sha256'],path
 print('PASS archive',p.name)
