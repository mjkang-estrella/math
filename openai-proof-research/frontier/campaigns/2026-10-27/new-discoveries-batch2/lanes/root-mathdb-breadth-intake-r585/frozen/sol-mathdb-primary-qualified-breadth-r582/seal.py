from pathlib import Path
import hashlib,json
D=Path(__file__).parent
files=[]
for p in sorted(D.rglob('*')):
 if not p.is_file() or p.name in ['manifest.json','final-verification-receipt.json']:continue
 b=p.read_bytes();files.append({'path':str(p.relative_to(D)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','final-verification-receipt.json'],'files':files},indent=2)+'\n')
