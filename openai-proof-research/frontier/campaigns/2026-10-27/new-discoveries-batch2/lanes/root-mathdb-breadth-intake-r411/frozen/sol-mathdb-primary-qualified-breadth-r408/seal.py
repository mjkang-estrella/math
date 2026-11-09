import pathlib,json,hashlib
L=pathlib.Path(__file__).resolve().parent
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and str(p.relative_to(L)) not in {'manifest.json','finalreceipt.json'}:
  b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(L/'manifest.json').write_text(json.dumps({'files':files},indent=2)+'\n');print('Sealed',len(files),'payload files')
