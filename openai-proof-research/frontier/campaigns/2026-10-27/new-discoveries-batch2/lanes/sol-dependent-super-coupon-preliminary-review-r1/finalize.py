from pathlib import Path
import hashlib,json,datetime
L=Path(__file__).resolve().parent
def sha(p):return hashlib.sha256(p.read_bytes()).hexdigest()
excluded={'finalmanifest.json','verification-receipt.json'}
files=[{'path':str(p.relative_to(L)),'bytes':p.stat().st_size,'sha256':sha(p)} for p in sorted(L.rglob('*')) if p.is_file() and p.name not in excluded]
(L/'finalmanifest.json').write_text(json.dumps({'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'excludes':sorted(excluded),'files':files},indent=2)+'\n')
print('Manifest:',len(files),'files; excludes itself and receipt.')
