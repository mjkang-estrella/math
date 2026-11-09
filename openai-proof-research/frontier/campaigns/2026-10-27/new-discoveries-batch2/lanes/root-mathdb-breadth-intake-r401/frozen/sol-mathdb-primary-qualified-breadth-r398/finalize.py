from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in {'manifest.json','final-receipt.json'}:
  d=p.read_bytes();files.append(dict(path=str(p.relative_to(O)),size=len(d),sha256=hashlib.sha256(d).hexdigest()))
(O/'manifest.json').write_text(json.dumps(dict(excludes=['manifest.json','final-receipt.json'],files=files),indent=2)+'\n')
print('payload files',len(files))
