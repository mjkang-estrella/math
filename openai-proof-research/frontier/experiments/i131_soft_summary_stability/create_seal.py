"""Development-only, exclusive one-time seal creator. The offline verifier never calls it."""
from pathlib import Path
import sys,os,json,hashlib,subprocess
sys.dont_write_bytecode=True
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i131_soft_summary_stability';E='frontier/experiments/i131_soft_summary_stability'
REPORT='frontier/iterations/i131-soft-summary-stability.md';seal=ROOT/S/'seal.json'
assert not seal.exists(),'one final seal only; repair/reseal forbidden'
paths={REPORT}
for base in [S,E]:
 for p in (ROOT/base).rglob('*'):
  assert not p.is_symlink()
  if p.is_file():paths.add(str(p.relative_to(ROOT)))
rows=[]
for p in sorted(paths):
 b=(ROOT/p).read_bytes();rows.append(dict(path=p,bytes=len(b),sha256=hashlib.sha256(b).hexdigest()))
assert [r['path'] for r in rows]==sorted(set(r['path'] for r in rows))
identity=hashlib.sha256(json.dumps(rows,sort_keys=True,separators=(',',':')).encode()).hexdigest()
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
r=subprocess.run([sys.executable,'-B',E+'/verify.py','--preseal'],cwd=ROOT,env=env,capture_output=True,text=True)
assert r.returncode==0,(r.stdout,r.stderr)
result=json.loads(r.stdout)
assert result['status']=='PRESEAL PASS' and result['validated_inventory_sha256']==identity
# Recheck immutable bytes immediately before the exclusive creation.
for row in rows:
 b=(ROOT/row['path']).read_bytes();assert len(b)==row['bytes'] and hashlib.sha256(b).hexdigest()==row['sha256']
data=dict(schema='i131-exact-owned-v1',pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',roots=[REPORT,S+'/',E+'/'],files=rows,validated_inventory_sha256=identity,preseal_result=result,scope='inventory envelope, not a signature or self-hash; one final seal')
with seal.open('x') as f:json.dump(data,f,indent=2,sort_keys=True);f.write('\n')
print(json.dumps(dict(status='SEALED ONCE',files=len(rows),seal_sha256=hashlib.sha256(seal.read_bytes()).hexdigest(),validated_inventory_sha256=identity)))
