"""Independent payload enumeration and manifest generation; no network."""
from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
rows=[dict(path=str(p.relative_to(L)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in sorted(L.rglob('*')) if p.is_file() and p.name not in ['finalmanifest.json','final-verification.json']]
(L/'finalmanifest.json').write_text(json.dumps(rows,indent=2)+'\n')
print('independent manifest entries',len(rows))
