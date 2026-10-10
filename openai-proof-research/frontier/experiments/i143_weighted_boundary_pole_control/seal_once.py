"""Authoring-only exclusive seal. Never imported or executed by offline replay."""
from pathlib import Path
import subprocess,sys,os,json,hashlib
ROOT=Path(__file__).resolve().parents[3]
S='frontier/sources/i143_weighted_boundary_pole_control'
E='frontier/experiments/i143_weighted_boundary_pole_control'
REPORT='frontier/iterations/i143-weighted-boundary-pole-control.md'
seal=ROOT/S/'seal.json'
assert not seal.exists(),'one seal only; no repair or reseal'
env=dict(os.environ,PYTHONDONTWRITEBYTECODE='1')
r=subprocess.run([sys.executable,'-B',E+'/verify.py','--preseal'],cwd=ROOT,env=env,capture_output=True,text=True)
assert r.returncode==0,(r.stdout,r.stderr)
receipt=json.loads(r.stdout);assert receipt['status']=='PASS' and receipt['preseal']
paths={REPORT}
for base in (S,E):
 for p in (ROOT/base).rglob('*'):
  assert not p.is_symlink()
  if p.is_file():paths.add(str(p.relative_to(ROOT)))
files=[]
for p in sorted(paths):
 b=(ROOT/p).read_bytes();files.append(dict(path=p,sha256=hashlib.sha256(b).hexdigest(),bytes=len(b)))
inv=hashlib.sha256(json.dumps(files,sort_keys=True,separators=(',',':')).encode()).hexdigest()
assert inv==receipt['validated_inventory_sha256'],'bytes changed since prevalidation'
obj=dict(schema='i143-exact-owned-v1',pin='fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb',roots=[REPORT,S+'/',E+'/'],files=files,validated_inventory_sha256=inv,prevalidation=receipt,scope='finite immutable evidence and identities only; not PDE proofs or contribution certification')
with seal.open('x') as f:
 f.write(json.dumps(obj,sort_keys=True,indent=2)+'\n');f.flush();os.fsync(f.fileno())
print(json.dumps(dict(status='SEALED ONCE',files=len(files),validated_inventory_sha256=inv,seal_sha256=hashlib.sha256(seal.read_bytes()).hexdigest()),indent=2))
