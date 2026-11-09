from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;ex={'manifest.json','final-verification-receipt.json'};rows=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in ex:
  b=p.read_bytes();rows.append(dict(path=str(p.relative_to(D)),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(D/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=sorted(ex),files=rows),indent=2)+'\n')
print('sealed',len(rows))
