from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[1]
files=[{'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size} for p in sorted(R.rglob('*')) if p.is_file() and p.name not in ['manifest.json','verification-receipt.json']]
(R/'manifest.json').write_text(json.dumps({'files':files},indent=2)+'\n');print('sealed',len(files),'files')
