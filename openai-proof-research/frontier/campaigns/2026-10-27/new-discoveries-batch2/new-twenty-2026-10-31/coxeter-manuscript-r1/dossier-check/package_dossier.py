from pathlib import Path
import hashlib,json,zipfile,datetime
w=Path(__file__).resolve().parent
excluded={'tools','render','dossier-check'}
files=[]
for p in w.rglob('*'):
 if not p.is_file() or any(x in excluded for x in p.relative_to(w).parts):continue
 if p.suffix in ['.olean','.ilean','.png']:continue
 if p.name in ['dossier-manifest.json','dossier.zip','archive-receipt.json']:continue
 files.append(p)
m={'scope':'DRAFT_ONLY; source body HOLD; credit0; no external dependency rebuild','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'files':{str(p.relative_to(w)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(files)}}
(w/'dossier-manifest.json').write_text(json.dumps(m,indent=2)+'\n')
with zipfile.ZipFile(w/'dossier.zip','w',zipfile.ZIP_DEFLATED) as z:
 for p in sorted(files)+[w/'dossier-manifest.json']:z.write(p,p.relative_to(w))
r={'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'file':'dossier.zip','sha256':hashlib.sha256((w/'dossier.zip').read_bytes()).hexdigest(),'bytes':(w/'dossier.zip').stat().st_size,'entries':len(files)+1,'manifest_sha256':hashlib.sha256((w/'dossier-manifest.json').read_bytes()).hexdigest()}
(w/'archive-receipt.json').write_text(json.dumps(r,indent=2)+'\n');print(r)
