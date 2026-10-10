"""Initial own-artifact seal writer. Refuses to refresh any existing seal."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i64_entropy_coefficient_extraction_novelty';E=R/'frontier/experiments/i64_entropy_coefficient_extraction_novelty';report=R/'frontier/reviews/i64-entropy-coefficient-extraction-novelty.md'
exclude={S/'seal.json',E/'verification.json'}
files=sorted([p for root in [S,E] for p in root.rglob('*') if p.is_file() and p not in exclude]+[report])
rows=[dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in files]
with (S/'seal.json').open('x') as f:json.dump(dict(artifacts=rows,limitation='I64 own artifact seal only; no analytic or priority certification.'),f,indent=2);f.write('\n')
print(len(rows))
