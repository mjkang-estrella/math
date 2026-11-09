import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and str(p.relative_to(L)) not in {'manifest.json','verification-receipt.json'}:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(L)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(L/'manifest.json').write_text(json.dumps({'files':files},indent=2)+'\n');print('Manifest payload files:',len(files))
