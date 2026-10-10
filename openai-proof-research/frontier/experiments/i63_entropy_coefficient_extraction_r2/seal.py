"""One-time seal writer for I63 only; never refreshes a prior or existing seal."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i63_entropy_coefficient_extraction_r2';E=R/'frontier/experiments/i63_entropy_coefficient_extraction_r2'
REPORT=R/'frontier/reviews/i63-entropy-coefficient-extraction-r2.md';excluded={S/'seal.json',E/'verification.json'}
paths=sorted({p for folder in [S,E] for p in folder.rglob('*') if p.is_file() and p not in excluded}|{REPORT})
rows=[dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in paths]
with (S/'seal.json').open('x') as f:json.dump(dict(artifacts=rows,scope='I63 only, one-shot seal; provenance does not imply analytic validity'),f,indent=2,sort_keys=True);f.write('\n')
print(len(rows))
