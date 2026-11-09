from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
files={str(p.relative_to(L)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(L.rglob('*')) if p.is_file() and str(p.relative_to(L)) not in ['final-manifest.json','final-verification-receipt.json']}
(L/'final-manifest.json').write_text(json.dumps({'files':files},indent=2)+'\n');print(json.dumps({'files':len(files)}))
