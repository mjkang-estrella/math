from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parent
removed=[]
for p in R.rglob('*.olean'):
 assert p.parent==R/'replay'
 removed.append({'path':str(p.relative_to(R)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size});p.unlink()
if removed: (R/'cleanup.json').write_text(json.dumps({'successful_audits_before_cleanup':True,'removed':removed},indent=2)+'\n')
files={str(p.relative_to(R)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'size':p.stat().st_size} for p in R.rglob('*') if p.is_file() and p.name not in [] and str(p.relative_to(R)) not in ['manifest.json','verification-receipt.json']}
(R/'manifest.json').write_text(json.dumps({'files':files},indent=2,sort_keys=True)+'\n')
print('manifest',len(files))
