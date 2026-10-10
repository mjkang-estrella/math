"""Prevalidate this round, then create its only seal. No reseal or repair mode."""
from pathlib import Path
import json,hashlib,subprocess,sys,time
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i157_dimension_independent_oracle_tolerance_r2'
E=R/'frontier/experiments/i157_dimension_independent_oracle_tolerance_r2'
REPORT='frontier/reviews/i157-dimension-independent-oracle-tolerance-r2.md'
assert not (S/'seal.json').exists()
assert not (E/'validation.json').exists()
def sha(b):return hashlib.sha256(b).hexdigest()
paths={REPORT,str((S/'inventory.json').relative_to(R)),str((E/'validation.json').relative_to(R))}
for root in [S,E]:
    for p in root.rglob('*'):
        assert not p.is_symlink()
        if p.is_file():paths.add(str(p.relative_to(R)))
owned=sorted(paths)
(S/'inventory.json').write_text(json.dumps(dict(owned_paths=owned,seal_path=str((S/'seal.json').relative_to(R)),allowed_live_ledger_drift=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],scope='Exact owned inventory. Review is incomplete; byte verification does not change its verdict.'),indent=2)+'\n')
prospective={p:sha((R/p).read_bytes()) for p in owned if p!=str((E/'validation.json').relative_to(R))}
start=time.monotonic()
proc=subprocess.run([sys.executable,'-B',str(E/'verify.py'),'--preseal'],cwd=R,input=json.dumps(prospective),text=True,capture_output=True)
if proc.returncode:
    print(proc.stdout);print(proc.stderr,file=sys.stderr)
    raise SystemExit(proc.returncode)
result=json.loads(proc.stdout)
assert result['status']=='PASS' and result['original_proof_verdict']=='unresolved'
for p,h in prospective.items():assert sha((R/p).read_bytes())==h,('changed during validation',p)
validation=dict(status='PASS',exit_code=proc.returncode,elapsed_seconds=time.monotonic()-start,stdout=proc.stdout,stderr=proc.stderr,result=result,scope='Read-only prevalidation before exclusive-create seal; no new finite diagnostics executed yet.')
(E/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
hashes={p:sha((R/p).read_bytes()) for p in owned}
with (S/'seal.json').open('x') as f:json.dump(dict(sha256=hashes,original_proof_verdict='unresolved',task_status='INCOMPLETE',seal_count=1),f,indent=2);f.write('\n')
print(json.dumps(dict(status='SEALED',owned_files=len(owned),seal_sha256=sha((S/'seal.json').read_bytes()),original_proof_verdict='unresolved',task_status='INCOMPLETE')))
