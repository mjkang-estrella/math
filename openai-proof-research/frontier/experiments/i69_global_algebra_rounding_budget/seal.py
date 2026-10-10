"""One-shot I69 seal writer; not run by verifier and never touches old seals."""
from pathlib import Path
import hashlib,json
ROOT=Path(__file__).resolve().parents[3]
SRC=ROOT/'frontier/sources/i69_global_algebra_rounding_budget'
EXP=ROOT/'frontier/experiments/i69_global_algebra_rounding_budget'
REPORT=ROOT/'frontier/iterations/i69-global-algebra-rounding-budget.md'
excluded={SRC/'seal.json',SRC/'verification.json'}
paths=[p for base in [SRC,EXP] for p in base.rglob('*') if p.is_file() and p not in excluded]+[REPORT]
files=[{'path':str(p.relative_to(ROOT)),'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in sorted(paths)]
(SRC/'seal.json').write_text(json.dumps({'pinned_commit':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','scope':'I69 artifact integrity only; not proof or novelty acceptance','files':files},indent=2,sort_keys=True)+'\n')
print(json.dumps({'sealed_artifacts':len(files)}))
