from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.relative_to(L).as_posix() not in ['manifest.json','final-receipt.json']:
  b=p.read_bytes();files.append({'path':p.relative_to(L).as_posix(),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'manifest.json').write_text(json.dumps({'files':files,'excluded_only':['manifest.json','final-receipt.json']},indent=2)+'\n')
print('Manifest files:',len(files))
