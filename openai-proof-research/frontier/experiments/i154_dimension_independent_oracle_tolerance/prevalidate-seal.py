"""Prepare inventory, run ONLY I154 read-only prevalidation, then exclusive-create ONE seal.
Use --check to stop after successful prevalidation without creating a seal.
No ancestor execution, repair, or reseal capability.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,time,datetime
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i154_dimension_independent_oracle_tolerance'
E='frontier/experiments/i154_dimension_independent_oracle_tolerance'
REPORT='frontier/iterations/i154-dimension-independent-oracle-tolerance.md'
assert sys.argv[1:] in ([],['--check'])
assert not (R/S/'seal.json').exists(),'No repair or resealing permitted'
def sha(p):return hashlib.sha256((R/p).read_bytes()).hexdigest()
paths={REPORT,S+'/inventory.json',E+'/validation.json'}
for base in [S,E]:
 for p in (R/base).rglob('*'):
  assert not p.is_symlink()
  if p.is_file():paths.add(str(p.relative_to(R)))
assert not any('__pycache__' in p or p.endswith('.pyc') for p in paths)
owned=sorted(paths)
inv={'owned_paths':owned,'seal_path':S+'/seal.json','allowed_live_ledger_drift':['README.md','frontier/README.md','frontier/TEN-FINDINGS.md','frontier/iterations/README.md'],'scope':'Exact canonical owned inventory; seal is exclusive-created only after successful read-only prevalidation.'}
(R/S/'inventory.json').write_text(json.dumps(inv,indent=2)+'\n')
hashes={p:sha(p) for p in owned if p!=E+'/validation.json'}
cmd=[sys.executable,'-B',str(R/E/'verify.py'),'--preseal'];start=time.monotonic()
r=subprocess.run(cmd,cwd=R,input=json.dumps(hashes),text=True,capture_output=True)
elapsed=time.monotonic()-start
if r.returncode:
 print(r.stdout);print(r.stderr,file=sys.stderr)
 raise SystemExit(r.returncode)
result=json.loads(r.stdout);assert result['status']=='PASS'
validation={'status':'PASS','command':['python3','-B',E+'/verify.py','--preseal'],'exit_code':r.returncode,'elapsed_seconds':elapsed,'stdout':r.stdout,'stderr':r.stderr,'result':result,'scope':'Read-only immutable preflight before only new finite diagnostics. Not proof or contribution certification.'}
(R/E/'validation.json').write_text(json.dumps(validation,indent=2)+'\n')
for p,h in hashes.items():assert sha(p)==h,('changed since prevalidation',p)
assert sorted(str(p.relative_to(R)) for b in [S,E] for p in (R/b).rglob('*') if p.is_file())==sorted(set(owned)-{REPORT})
if sys.argv[1:]==['--check']:
 print(json.dumps({'status':'PASS','mode':'prevalidated, NOT sealed','elapsed_seconds':elapsed,'result':result},indent=2))
else:
 final={p:sha(p) for p in owned}
 with (R/S/'seal.json').open('x') as f:
  json.dump({'sha256':final,'utc':datetime.datetime.now(datetime.timezone.utc).isoformat(),'scope':'One immutable seal; evidence and finite diagnostics only, not universal proof or acceptance.'},f,indent=2);f.write('\n')
 print(json.dumps({'status':'PASS','mode':'sealed once after prevalidation','owned_files':len(owned),'elapsed_seconds':elapsed,'seal_sha256':sha(S+'/seal.json'),'result':result},indent=2))
