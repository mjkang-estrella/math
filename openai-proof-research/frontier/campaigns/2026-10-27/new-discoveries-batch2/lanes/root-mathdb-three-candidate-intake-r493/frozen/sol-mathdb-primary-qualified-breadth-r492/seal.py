from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parent
files=[]
for p in sorted(D.rglob('*')):
 if p.is_file() and p.relative_to(D).as_posix() not in ['manifest.json','verification-receipt.json']:
  b=p.read_bytes();files.append({'path':p.relative_to(D).as_posix(),'size':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(D/'manifest.json').write_text(json.dumps({'excluded_exact_paths':['manifest.json','verification-receipt.json'],'files':files},indent=2)+'\n')
print('sealed',len(files),'files')
