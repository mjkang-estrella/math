from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parent;excluded=['manifest.json','final-verification-receipt.json'];files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and str(p.relative_to(D)) not in excluded:
  b=p.read_bytes();files.append(dict(path=str(p.relative_to(D)),sha256=hashlib.sha256(b).hexdigest(),size=len(b)))
(D/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=excluded,files=files),indent=2)+'\n')
b=(D/'manifest.json').read_bytes();print(json.dumps(dict(manifest_sha256=hashlib.sha256(b).hexdigest(),manifest_size=len(b),payload_files=len(files))))
