from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
rows=[]
for p in sorted(L.rglob('*')):
 if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']:
  b=p.read_bytes();rows.append(dict(path=str(p.relative_to(L)),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(L/'manifest.json').write_text(json.dumps(dict(files=rows),indent=2)+'\n');print('sealed',len(rows))
