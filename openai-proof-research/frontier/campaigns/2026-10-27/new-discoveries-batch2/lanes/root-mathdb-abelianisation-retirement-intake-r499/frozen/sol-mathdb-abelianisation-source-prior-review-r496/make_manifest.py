from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
excluded=['manifest.json','final-receipt.json']
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in excluded:
  b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':excluded,'files':files},indent=2)+'\n')
print('Manifest payloads:',len(files))
