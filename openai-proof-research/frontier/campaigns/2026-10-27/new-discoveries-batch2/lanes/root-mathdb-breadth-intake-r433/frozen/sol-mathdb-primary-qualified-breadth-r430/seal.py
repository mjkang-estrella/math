from pathlib import Path
import hashlib,json
O=Path(__file__).resolve().parent
excluded={'manifest.json','final-receipt.json'}
files=[]
for p in sorted(O.rglob('*')):
 if p.is_file() and str(p.relative_to(O)) not in excluded:
  b=p.read_bytes();files.append({'path':str(p.relative_to(O)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(O/'manifest.json').write_text(json.dumps({'files':files,'excluded':sorted(excluded)},indent=2)+'\n')
print('sealed',len(files))
