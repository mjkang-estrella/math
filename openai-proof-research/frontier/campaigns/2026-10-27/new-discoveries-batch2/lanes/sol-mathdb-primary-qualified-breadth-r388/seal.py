from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
entries=[]
for p in sorted(R.rglob('*')):
 if not p.is_file() or str(p.relative_to(R)) in {'manifest.json','verification-receipt.json'}:continue
 b=p.read_bytes();entries.append({'path':str(p.relative_to(R)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(R/'manifest.json').write_text(json.dumps({'files':entries,'excluded':['manifest.json','verification-receipt.json']},indent=2)+'\n')
print('sealed',len(entries),'payload files')
