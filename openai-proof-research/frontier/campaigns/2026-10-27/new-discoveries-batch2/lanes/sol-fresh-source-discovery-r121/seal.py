from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
files={}
for p in sorted(L.rglob('*')):
    if not p.is_file() or p.name=='finalmanifest.json':continue
    h=hashlib.sha256()
    with p.open('rb') as f:
        while b:=f.read(65536):h.update(b)
    files[str(p.relative_to(L))]={'bytes':p.stat().st_size,'sha256':h.hexdigest()}
(L/'finalmanifest.json').write_text(json.dumps({'scope':'All lane files except this self-referential manifest; scientific sufficiency separate from integrity','files':files},indent=2)+'\n')
print('sealed',len(files),'files')
