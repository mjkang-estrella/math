"""Initial seal only. Refuses to refresh an existing artifact seal."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i38_propeller_stability_novelty_r3';E=Path(__file__).resolve().parent
p=S/'artifact-seal.json';assert not p.exists(),'Refusing to refresh existing seal'
excluded={p,E/'verification.json',E/'prior-reproduction.json'}
files=[R/'frontier/reviews/i38-propeller-stability-novelty-r3.md']
for root in [S,E]:files += [x for x in root.rglob('*') if x.is_file() and x not in excluded and '__pycache__' not in x.parts]
rows=[{'path':str(x.relative_to(R)),'bytes':x.stat().st_size,'sha256':hashlib.sha256(x.read_bytes()).hexdigest()} for x in sorted(files)]
p.write_text(json.dumps({'policy':'Initial immutable review seal. Excludes itself, __pycache__, and regenerated verification.json/prior-reproduction.json. check.py output is deterministic and sealed. No author or R2 seal refresh.','files':rows},indent=2)+'\n');print({'sealed_artifacts':len(rows)})
