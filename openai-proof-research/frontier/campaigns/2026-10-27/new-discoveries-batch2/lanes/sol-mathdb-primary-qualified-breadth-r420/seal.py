from pathlib import Path
import json,hashlib
W=Path(__file__).resolve().parent
ex={'manifest.json','final-verification-receipt.json'}
files=[]
for p in sorted(W.rglob('*')):
 if p.is_file() and str(p.relative_to(W)) not in ex:
  b=p.read_bytes();files.append({'path':str(p.relative_to(W)),'sha256':hashlib.sha256(b).hexdigest(),'size':len(b)})
(W/'manifest.json').write_text(json.dumps({'files':files,'excluded_exact_relative_paths':sorted(ex)},indent=2)+'\n')
print('sealed',len(files),'payload files')
