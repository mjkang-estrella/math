"""Preparation-only sorted exact owned inventory. No seals are modified."""
from pathlib import Path
import json
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i142_uniform_algebraic_allocation';E=R/'frontier/experiments/i142_uniform_algebraic_allocation'
assert not (S/'seal.json').exists()
paths={str(p.relative_to(R)) for base in [S,E] for p in base.rglob('*') if p.is_file()}
paths.update(['frontier/iterations/i142-uniform-algebraic-allocation.md',str((E/'validation.json').relative_to(R)),str((S/'inventory.json').relative_to(R))])
obj=dict(owned_paths=sorted(paths),seal_path=str((S/'seal.json').relative_to(R)),allowed_live_ledger_drift=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'])
(S/'inventory.json').write_text(json.dumps(obj,indent=2)+'\n');print(len(paths))
