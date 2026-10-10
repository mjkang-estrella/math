"""Create this iteration's first seal only. Refuses to overwrite any seal."""
from pathlib import Path
import hashlib,json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i60_threshold_structural_combinatorics_discovery';E=Path(__file__).resolve().parent
out=S/'seal.json'
if out.exists():raise SystemExit('Existing seal is immutable; refusing to refresh it.')
report='frontier/iterations/i60-threshold-structural-combinatorics-discovery.md'
excluded=[str(out.relative_to(R)),str((S/'verification.json').relative_to(R))]
files=sorted([p for root in [S,E] for p in root.rglob('*') if p.is_file() and str(p.relative_to(R)) not in excluded]+[R/report])
rows=[dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest(),bytes=p.stat().st_size) for p in files]
out.write_text(json.dumps(dict(report=report,excluded=excluded,files=rows),indent=2)+'\n')
print(json.dumps(dict(sealed=len(rows))))
