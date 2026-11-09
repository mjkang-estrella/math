from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent
files=[p for p in R.rglob('*') if p.is_file() and str(p.relative_to(R)) not in {'manifest.json','final-receipt.json'}]
(R/'manifest.json').write_text(json.dumps({'files':[{'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size} for p in sorted(files)]},indent=2)+'\n')
