"""One-time I61 seal creation, separate from read-only verification."""
from pathlib import Path
import hashlib,json,datetime
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i61_averaged_entropy_coefficient_rounding'
E=ROOT/'frontier/experiments/i61_averaged_entropy_coefficient_rounding'
REPORT=ROOT/'frontier/iterations/i61-averaged-entropy-coefficient-rounding.md'
if (S/'seal.json').exists():raise SystemExit('Refuse to overwrite existing I61 seal')
excluded={S/'seal.json',E/'verification.json'}
files={p for d in [S,E] for p in d.rglob('*') if p.is_file() and p not in excluded}|{REPORT}
rows=[dict(path=str(p.relative_to(ROOT)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in sorted(files)]
obj=dict(created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),artifacts=rows,excluded=[str(p.relative_to(ROOT)) for p in sorted(excluded)],scope='Only new I61 paths; no previous seal altered. Verification output excluded to prevent circularity.')
(S/'seal.json').write_text(json.dumps(obj,indent=2)+'\n')
print(json.dumps(dict(artifacts=len(rows),seal_sha256=hashlib.sha256((S/'seal.json').read_bytes()).hexdigest())))
