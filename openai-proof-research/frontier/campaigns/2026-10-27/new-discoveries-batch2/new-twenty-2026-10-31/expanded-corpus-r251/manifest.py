from pathlib import Path
import hashlib,json
L=Path(__file__).resolve().parent
out={str(p.relative_to(L)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in sorted(L.rglob('*')) if p.is_file() and p.name!='manifest.json'}
(L/'manifest.json').write_text(json.dumps(out,indent=2));print('manifest',len(out),'files')
