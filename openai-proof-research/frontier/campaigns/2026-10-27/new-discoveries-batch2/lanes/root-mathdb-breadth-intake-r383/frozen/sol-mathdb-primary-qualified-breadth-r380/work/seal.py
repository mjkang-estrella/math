from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parents[1];files=[]
for p in sorted(R.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']:
  b=p.read_bytes();files.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(R/'manifest.json').write_text(json.dumps({'schema_version':1,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'excluded_only':['manifest.json','verification-receipt.json'],'files':files},indent=2)+'\n')
