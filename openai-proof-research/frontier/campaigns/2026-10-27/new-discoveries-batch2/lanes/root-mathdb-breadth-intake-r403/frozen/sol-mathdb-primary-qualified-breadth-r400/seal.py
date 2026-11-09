from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent
out=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p.name not in ('manifest.json','final-receipt.json'):
  b=p.read_bytes();out.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(O/'manifest.json').write_text(json.dumps({'files':out,'excludes_only':['manifest.json','final-receipt.json']},indent=2)+'\n')
