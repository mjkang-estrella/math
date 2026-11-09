from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parents[1]
rows=[]
for p in sorted(L.rglob('*')):
 if not p.is_file() or str(p.relative_to(L)) in {'manifest.json','verification-receipt.json'}:continue
 b=p.read_bytes();rows.append({'path':str(p.relative_to(L)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(L/'manifest.json').write_text(json.dumps({'files':rows,'excluded_only':['manifest.json','verification-receipt.json']},indent=2)+'\n')
print('sealed',len(rows),'files')
