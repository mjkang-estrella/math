"""One-time seal preparation, explicitly separate from read-only verify.py."""
import hashlib,json
from pathlib import Path
ROOT=Path(__file__).resolve().parents[3]
S=ROOT/'frontier/sources/i108_galois_tuple_divisibility'
E=ROOT/'frontier/experiments/i108_galois_tuple_divisibility'
REPORT=ROOT/'frontier/iterations/i108-galois-tuple-divisibility.md'
def digest(p):return hashlib.sha256(p.read_bytes()).hexdigest()
def main():
 assert not (S/'seal.json').exists() and not (S/'seal.sha256').exists(),'Seal already exists; never reseal'
 validation=json.loads((S/'validation-before-seal.json').read_text())
 assert validation['exit_code']==0 and validation['result']['status']=='PASS'
 assert (ROOT/validation['attempt_path']).read_bytes()==(S/'validation-before-seal.json').read_bytes()
 current=sorted([str(REPORT.relative_to(ROOT))]+[str(p.relative_to(ROOT)) for d in [S,E] for p in d.rglob('*') if p.is_file()])
 allowed={str((S/'validation-before-seal.json').relative_to(ROOT)),validation['attempt_path']}
 assert set(current)==set(validation['checked_files'])|allowed,'Unvalidated inventory change'
 for p,h in validation['checked_files'].items():assert digest(ROOT/p)==h,'Unvalidated change: '+p
 for r in json.loads((S/'immutable-references.json').read_text()):assert digest(ROOT/r['path'])==r['sha256'],'Immutable reference change'
 files={p:digest(ROOT/p) for p in current}
 seal={'pin':'fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb','owned_inventory':sorted(current+[str((S/'seal.json').relative_to(ROOT)),str((S/'seal.sha256').relative_to(ROOT))]),'files':files,'drift_allowed_live_only':['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],'limitations':'Evidence integrity and finite checks only. No universal proof, contribution certification, human review or priority assertion.'}
 raw=(json.dumps(seal,indent=2,sort_keys=True)+'\n').encode()
 with (S/'seal.json').open('xb') as f:f.write(raw)
 with (S/'seal.sha256').open('x') as f:f.write(hashlib.sha256(raw).hexdigest()+'\n')
 print(json.dumps({'owned_files':len(seal['owned_inventory']),'seal_sha256':hashlib.sha256(raw).hexdigest()}))
if __name__=='__main__':main()
