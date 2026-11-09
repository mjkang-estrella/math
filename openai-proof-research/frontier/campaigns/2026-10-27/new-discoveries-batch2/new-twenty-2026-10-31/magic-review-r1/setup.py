from pathlib import Path
import hashlib,json,zipfile,shutil
r=Path(__file__).resolve().parent;s=r.parent/'expanded-corpus-r75'
for x in ['scripts','logs','receipts','sources','extracted']: (r/x).mkdir(exist_ok=True)
def manifest(): return {str(p.relative_to(s)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(s.rglob('*')) if p.is_file()}
(r/'receipts/input-before.json').write_text(json.dumps(manifest(),indent=2))
with zipfile.ZipFile(s/'magic-proof-source.zip') as z:
 for i in z.infolist():
  p=Path(i.filename); assert not p.is_absolute() and '..' not in p.parts and not ((i.external_attr>>16)&0o170000)==0o120000
 z.extractall(r/'extracted')
print([str(p.relative_to(r)) for p in (r/'extracted').rglob('*')]);print('files',len(manifest()))
