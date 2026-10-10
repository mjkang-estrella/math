"""One-time explicit seal creation; never called by read-only verifier."""
from pathlib import Path
import json,hashlib,datetime
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i86_compact_solenoidal_computation_novelty_r3';E=R/'frontier/experiments/i86_compact_solenoidal_computation_novelty_r3';P=R/'frontier/reviews/i86-compact-solenoidal-computation-novelty-r3.md';seal=S/'seal-v1.json';anchor=S/'anchor.json'
assert not seal.exists() and not anchor.exists(),'Refuse reseal'
files=sorted([p for d in [S,E] for p in d.rglob('*') if p.is_file()]+[P])
rows=[]
for p in files:
 b=p.read_bytes();rows.append(dict(path=str(p.relative_to(R)),bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
d=dict(schema='I86-evidence-seal-v1',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',scope='Conditional TECHNICAL contribution verdict only. No original-proof PASS or finding acceptance.',self_exclusions=[str(seal.relative_to(R)),str(anchor.relative_to(R))],files=rows)
seal.write_text(json.dumps(d,indent=2)+'\n');digest=hashlib.sha256(seal.read_bytes()).hexdigest();anchor.write_text(json.dumps(dict(seal_sha256=digest),indent=2)+'\n');print(json.dumps(dict(files=len(rows),seal_sha256=digest),indent=2))
