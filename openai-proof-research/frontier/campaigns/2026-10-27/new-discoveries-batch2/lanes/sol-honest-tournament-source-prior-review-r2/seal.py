from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['final-manifest.json','final-verification.json']:
  b=p.read_bytes();rows.append({'path':str(p.relative_to(L)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'final-manifest.json').write_text(json.dumps({'sealed_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'excludes':['final-manifest.json','final-verification.json'],'files':rows},indent=2)+'\n')
print('sealed',len(rows),'files')
