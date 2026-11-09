from pathlib import Path
import hashlib,json
D=Path(__file__).resolve().parents[1]
manifest={str(p.relative_to(D)):{'sha256':hashlib.sha256(p.read_bytes()).hexdigest(),'bytes':p.stat().st_size} for p in D.rglob('*') if p.is_file() and p.name!='artifact-manifest.json' and not str(p.relative_to(D)).startswith('logs/seal.')}
(D/'outputs/artifact-manifest.json').write_text(json.dumps({'scope':'All lane files except this self-referential manifest and the currently written seal log/receipt.','files':manifest},indent=2)+'\n')
print(len(manifest),'artifacts sealed')
