from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
excluded=['final-receipt.json','manifest.json'];files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and str(p.relative_to(L)) not in excluded:
  b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'manifest.json').write_text(json.dumps({'excluded_paths':excluded,'files':files},indent=2)+'\n')
print(len(files),'payload files')
