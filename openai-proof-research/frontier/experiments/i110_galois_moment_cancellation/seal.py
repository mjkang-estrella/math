"""One-time seal writer; separate from, and never imported by, the verifier."""
import json,hashlib
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=Path('frontier/sources/i110_galois_moment_cancellation');E=Path('frontier/experiments/i110_galois_moment_cancellation')
R=Path('frontier/iterations/i110-galois-moment-cancellation.md')
assert not (ROOT/S/'seal.json').exists() and not (ROOT/S/'seal.sha256').exists(),'Refuse resealing'
validation=json.loads((ROOT/S/'validation-before-seal.json').read_text())
assert validation['exit_code']==0 and validation['result']['status']=='PASS'
paths=sorted([str(R)]+[str(p.relative_to(ROOT)) for d in [S,E] for p in (ROOT/d).rglob('*') if p.is_file()])
sha=lambda b:hashlib.sha256(b).hexdigest()
obj={'files':{p:sha((ROOT/p).read_bytes()) for p in paths},'owned_inventory':sorted(paths+[str(S/'seal.json'),str(S/'seal.sha256')]),
     'drift_allowed_live_only':['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],
     'boundary':'Evidence integrity and finite reproducibility only; no universal proof, priority or contribution certification.'}
b=(json.dumps(obj,indent=2)+'\n').encode();(ROOT/S/'seal.json').write_bytes(b);(ROOT/S/'seal.sha256').write_text(sha(b)+'\n')
print(json.dumps({'seal_sha256':sha(b),'owned_files':len(obj['owned_inventory'])}))
