from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
excluded={'manifest.json','final-receipt.json'}
files=[]
for p in sorted(R.rglob('*')):
 if p.is_file() and str(p.relative_to(R)) not in excluded:
  files.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
(R/'manifest.json').write_text(json.dumps({'excluded_exact_relative_paths':sorted(excluded),'files':files},sort_keys=True,indent=2)+'\n')
print('SEALED',len(files))
