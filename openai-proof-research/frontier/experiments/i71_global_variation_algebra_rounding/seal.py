"""Create the first I71 seal. Refuses overwrite, never refreshes old seals."""
from pathlib import Path
import json,hashlib
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i71_global_variation_algebra_rounding'
X=R/'frontier/experiments/i71_global_variation_algebra_rounding'
REPORT=R/'frontier/iterations/i71-global-variation-algebra-rounding.md'
target=S/'seal.json'
if target.exists():raise SystemExit('Refusing to overwrite existing seal.')
excluded={target,S/'verification.json'}
files=[p for base in [S,X] for p in base.rglob('*') if p.is_file() and p not in excluded]+[REPORT]
records=[dict(path=str(p.relative_to(R)),sha256=hashlib.sha256(p.read_bytes()).hexdigest()) for p in sorted(files)]
target.write_text(json.dumps(dict(pinned_commit='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',scope='I71 initial immutable seal; verification.json is an output only',files=records),indent=2,sort_keys=True)+'\n')
print(len(records))
