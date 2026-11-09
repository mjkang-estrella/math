from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[1]
entries=[]
for p in sorted(R.rglob('*')):
 if p.is_file() and str(p.relative_to(R)) not in ['manifest.json','verification-receipt.json']:
  b=p.read_bytes();entries.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(R/'manifest.json').write_text(json.dumps({'files':entries,'exclusions':['manifest.json','verification-receipt.json']},indent=2)+'\n')
print('Sealed',len(entries),'files')
