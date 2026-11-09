from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[1]
manifest={str(p.relative_to(D)):hashlib.sha256(p.read_bytes()).hexdigest() for p in sorted(D.rglob('*')) if p.is_file() and p.name!='artifact-manifest.json'}
(D/'artifact-manifest.json').write_text(json.dumps(manifest,indent=2)+'\n')
for name,h in manifest.items():assert hashlib.sha256((D/name).read_bytes()).hexdigest()==h
print('artifact hashes verified:',len(manifest))
