from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parent
files=[]
for p in sorted(R.rglob('*')):
 if p.is_file() and str(p.relative_to(R)) not in {'manifest.json','finalreceipt.json'}:
  files.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size})
(R/'manifest.json').write_text(json.dumps({'files':files,'excluded_exact_relative_paths':['manifest.json','finalreceipt.json']},indent=2)+'\n')
print('sealed',len(files),'payload files')
