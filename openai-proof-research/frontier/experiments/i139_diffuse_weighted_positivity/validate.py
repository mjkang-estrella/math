"""Preparation-only capture of the read-only verifier; no inherited program execution."""
from pathlib import Path
import subprocess,sys,time,json,hashlib
R=Path(__file__).resolve().parents[3];S=R/'frontier/sources/i139_diffuse_weighted_positivity';E=R/'frontier/experiments/i139_diffuse_weighted_positivity'
assert not (S/'seal.json').exists()
inv=json.loads((S/'inventory.json').read_text());vp=str((E/'validation.json').relative_to(R));paths=[p for p in inv['owned_paths'] if p!=vp]
def hashes():return {p:hashlib.sha256((R/p).read_bytes()).hexdigest() for p in paths}
before=hashes();cmd=[sys.executable,'-B',str((E/'verify.py').relative_to(R)),'--preseal'];start=time.monotonic();r=subprocess.run(cmd,cwd=R,text=True,capture_output=True);elapsed=time.monotonic()-start
assert hashes()==before,'Inputs changed during validation'
record=dict(status='PASS' if r.returncode==0 else 'FAIL',command=cmd,cwd=str(R),exit_code=r.returncode,elapsed_seconds=elapsed,stdout=r.stdout,stderr=r.stderr,validated_sha256=before)
if r.returncode==0:record['result']=json.loads(r.stdout)
(E/'validation.json').write_text(json.dumps(record,indent=2)+'\n')
print(json.dumps({k:v for k,v in record.items() if k not in ['stdout','validated_sha256','result']},indent=2));print(r.stdout)
assert r.returncode==0
