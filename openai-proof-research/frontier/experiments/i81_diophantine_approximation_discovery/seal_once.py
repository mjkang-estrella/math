"""One-time seal creator. Refuses to overwrite; not part of verification."""
from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i81_diophantine_approximation_discovery';E=R/'frontier/experiments/i81_diophantine_approximation_discovery';P=R/'frontier/iterations/i81-diophantine-approximation-discovery.md'
target=S/'seal.json'
if target.exists():raise SystemExit('Refusing to rewrite existing seal')
files=sorted([p for root in (S,E) for p in root.rglob('*') if p.is_file()]+[P])
obj={'format':'I81 immutable evidence seal v1','created_utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'pinned_commit':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','exact_owned_domain':[str(P.relative_to(R)),str(S.relative_to(R))+'/**',str(E.relative_to(R))+'/**'],'excluded_self':str(target.relative_to(R)),'mutable_ledgers':['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],'immutable_reference_manifest':str((S/'immutable-references.json').relative_to(R)),'artifacts':[{'path':str(p.relative_to(R)),'bytes':p.stat().st_size,'sha256':hashlib.sha256(p.read_bytes()).hexdigest()} for p in files]}
with target.open('x') as f:f.write(json.dumps(obj,indent=2,sort_keys=True)+'\n')
print(hashlib.sha256(target.read_bytes()).hexdigest())
