"""Seal only the explicitly authorized resumed paths; run after authoring finishes."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i26_probability_discovery_resumed';E=Path(__file__).resolve().parent
excluded={S/'artifact-seal.json',S/'artifact-seal.sha256',E/'verification.json'}
files={p for root in [S,E] for p in root.rglob('*') if p.is_file() and '__pycache__' not in p.parts}
files.add(R/'frontier/iterations/i26-probability-discovery-resumed.md')
entries=[]
for p in sorted(files-excluded):
 b=p.read_bytes();entries.append(dict(path=str(p.relative_to(R)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
raw=(json.dumps(dict(schema=1,scope='I26 resumed only; integrity is not proof acceptance',excluded=[str(p.relative_to(R)) for p in sorted(excluded)],files=entries),indent=2)+'\n').encode()
(S/'artifact-seal.json').write_bytes(raw);(S/'artifact-seal.sha256').write_text(hashlib.sha256(raw).hexdigest()+'\n')
print('sealed',len(entries),'artifacts')
