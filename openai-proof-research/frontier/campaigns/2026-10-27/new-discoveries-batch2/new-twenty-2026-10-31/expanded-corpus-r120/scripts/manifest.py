from pathlib import Path
import json,hashlib
D=Path(__file__).resolve().parents[1];files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.name!='MANIFEST.json' and not str(p.relative_to(D)).startswith('logs/manifest'):
  files.append({'path':str(p.relative_to(D)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()})
(D/'MANIFEST.json').write_text(json.dumps({'files':files,'excluded':['MANIFEST.json','logs/manifest* (active generation log/receipt)'],'limitation':'Hashes bind lane artifacts, not worldwide novelty or independent acceptance.'},indent=2)+'\n')
print(len(files),'files bound')
