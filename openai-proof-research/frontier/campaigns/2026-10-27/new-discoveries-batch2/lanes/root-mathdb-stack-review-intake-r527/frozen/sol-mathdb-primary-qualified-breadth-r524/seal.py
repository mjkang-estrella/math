from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent
files=[]
for p in sorted(O.rglob('*')):
 if not p.is_file() or p.relative_to(O).as_posix() in ['manifest.json','final-verification-receipt.json']:continue
 b=p.read_bytes();files.append(dict(path=p.relative_to(O).as_posix(),size=len(b),sha256=hashlib.sha256(b).hexdigest()))
(O/'manifest.json').write_text(json.dumps(dict(excluded_exact_paths=['manifest.json','final-verification-receipt.json'],files=files),indent=2)+'\n')
