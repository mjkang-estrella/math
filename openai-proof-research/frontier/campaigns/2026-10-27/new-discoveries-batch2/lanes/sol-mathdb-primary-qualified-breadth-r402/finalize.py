from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and p not in [O/'manifest.json',O/'final-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(O)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(O/'manifest.json').write_text(json.dumps({'files':files,'excludes_only':['manifest.json','final-receipt.json']},indent=2)+'\n')
print('manifest files',len(files))
