"""One-shot sealing of owned I85 files only; refuses to reseal."""
from pathlib import Path
import hashlib,json,datetime
R=Path(__file__).resolve().parents[3];E=Path(__file__).parent;S=R/'frontier/sources/i85_compact_solenoidal_computation_r2';p=S/'seal-v1.json'
assert not p.exists(),'Refusing to reseal'
files=[q for d in [S,E] for q in d.rglob('*') if q.is_file()]+[R/'frontier/reviews/i85-compact-solenoidal-computation-r2.md']
assert len(files)==len(set(files))
records=[]
for q in sorted(files):
 b=q.read_bytes();records.append(dict(path=str(q.relative_to(R)),sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
s=dict(schema='I85-owned-evidence-seal-v1',pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',created_utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),files=records,mutable_reference_exceptions=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],scope='Original-proof review; nomination HELD; evidence integrity is not contribution acceptance. No prior evidence resealed.')
p.write_text(json.dumps(s,indent=2)+'\n');print(json.dumps(dict(files=len(records),seal_sha256=hashlib.sha256(p.read_bytes()).hexdigest())))
