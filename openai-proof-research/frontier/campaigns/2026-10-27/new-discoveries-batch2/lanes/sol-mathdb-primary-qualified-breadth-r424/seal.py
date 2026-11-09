from pathlib import Path
import json,hashlib
O=Path(__file__).parent
excluded={'manifest.json','final-receipt.json'}
rows=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in excluded:
  b=p.read_bytes();rows.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(O/'manifest.json').write_text(json.dumps({'files':rows,'excluded_exact_relative_paths':sorted(excluded)},indent=2)+'\n')
print(len(rows))
