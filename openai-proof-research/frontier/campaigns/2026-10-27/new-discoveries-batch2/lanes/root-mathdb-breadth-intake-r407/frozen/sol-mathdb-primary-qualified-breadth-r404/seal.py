from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
files=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','finalreceipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(L)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'manifest.json').write_text(json.dumps({'excluded_only':['manifest.json','finalreceipt.json'],'files':files},indent=2)+'\n')
print('sealed',len(files))
