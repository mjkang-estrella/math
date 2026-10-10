"""Preparation only: build canonical inventory and run the read-only preseal check.
Never writes a seal. Does not execute any inherited verifier or diagnostics.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,time
sys.dont_write_bytecode=True
R=Path(__file__).resolve().parents[3]
S=R/'frontier/sources/i145_arithmetic_automorphic_discovery'
E=Path(__file__).resolve().parent
report='frontier/iterations/i145-arithmetic-automorphic-discovery.md'
assert not (S/'seal.json').exists(),'Already sealed; preparation forbidden'
owned={report,str((S/'inventory.json').relative_to(R)),str((E/'validation.json').relative_to(R))}
for base in (S,E):
 for p in base.rglob('*'):
  assert not p.is_symlink()
  if p.is_file():owned.add(str(p.relative_to(R)))
(S/'inventory.json').write_text(json.dumps(dict(owned_paths=sorted(owned),seal_path=str((S/'seal.json').relative_to(R)),allowed_live_ledger_drift=['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md']),indent=2)+'\n')
val=str((E/'validation.json').relative_to(R))
prospective={p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in sorted(owned) if p!=val}
t=time.monotonic()
p=subprocess.run([sys.executable,'-B',str(E/'verify.py'),'--preseal'],cwd=R,input=json.dumps(prospective),text=True,capture_output=True)
rec=dict(status='PASS' if p.returncode==0 else 'FAIL',exit_code=p.returncode,elapsed_seconds=time.monotonic()-t,stdout=p.stdout,stderr=p.stderr,prospective_sha256=prospective,scope='Preparation receipt; one flat read-only preflight, then only new finite diagnostics; no seal written')
(E/'validation.json').write_text(json.dumps(rec,indent=2)+'\n')
print(json.dumps({k:v for k,v in rec.items() if k not in ('prospective_sha256','stdout')},indent=2),flush=True)
if p.returncode==0:
 result=json.loads(p.stdout);print(json.dumps({k:v for k,v in result.items() if k!='new_finite_diagnostics'},indent=2))
else:print(p.stdout)
sys.exit(p.returncode)
