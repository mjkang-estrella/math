from pathlib import Path
import json,hashlib
O=Path(__file__).parent;excluded={'manifest.json','verification-receipt.json'}
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in excluded:
  b=p.read_bytes();files.append({'path':str(p.relative_to(O)),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(O/'manifest.json').write_text(json.dumps({'excluded_exact_paths':sorted(excluded),'files':files},indent=2)+'\n');print('Sealed',len(files),'payloads')
