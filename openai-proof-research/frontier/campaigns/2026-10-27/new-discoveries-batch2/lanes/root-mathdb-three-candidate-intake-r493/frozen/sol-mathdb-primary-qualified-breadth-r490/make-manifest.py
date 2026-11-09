from pathlib import Path
import json,hashlib
O=Path(__file__).resolve().parent
excluded=['manifest.json','final-receipt.json']
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in excluded:
  z=p.read_bytes();files.append(dict(path=str(p.relative_to(O)),size=len(z),sha256=hashlib.sha256(z).hexdigest()))
(O/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=excluded,files=files),indent=2)+'\n')
print('manifest payloads',len(files))
