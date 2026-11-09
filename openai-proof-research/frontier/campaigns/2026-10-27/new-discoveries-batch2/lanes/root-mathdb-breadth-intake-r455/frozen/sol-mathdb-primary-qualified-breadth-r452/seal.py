from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','final-receipt.json']:
  b=p.read_bytes();rows.append({'path':str(p.relative_to(L)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(L/'manifest.json').write_text(json.dumps({'schema':1,'lane':L.name,'excluded':['manifest.json','final-receipt.json'],'files':rows},indent=2)+'\n')
print('sealed',len(rows),'payload files')
