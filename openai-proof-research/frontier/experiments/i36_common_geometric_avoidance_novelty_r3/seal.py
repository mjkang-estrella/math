"""Explicit one-time artifact sealing; verification never invokes this script."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[3];S=ROOT/'frontier/sources/i36_common_geometric_avoidance_novelty_r3';E=ROOT/'frontier/experiments/i36_common_geometric_avoidance_novelty_r3'
files=[]
for base in (S,E):
 files.extend(p for p in base.rglob('*') if p.is_file() and '__pycache__' not in p.parts and p not in (S/'artifact-seal.json',E/'verification.json'))
files.append(ROOT/'frontier/reviews/i36-common-geometric-avoidance-novelty-r3.md')
rows=[]
for p in sorted(files):
 b=p.read_bytes();rows.append({'path':str(p.relative_to(ROOT)),'bytes':len(b),'sha256':hashlib.sha256(b).hexdigest()})
(S/'artifact-seal.json').write_text(json.dumps({'algorithm':'sha256','excludes':['self','owned generated verification.json'],'files':rows},indent=2,sort_keys=True)+'\n')
print(len(rows))
