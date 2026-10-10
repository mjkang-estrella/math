"""One-time prevalidation driver. This is not the offline verifier.
Writes only I148 validation and a single exclusive-create seal after PASS.
Cannot repair or reseal; fails if either receipt already exists.
"""
from pathlib import Path
import sys,json,hashlib,subprocess,time
R=Path(__file__).resolve().parents[3]
S='frontier/sources/i148_polynomial_index_torus_subpackets';E='frontier/experiments/i148_polynomial_index_torus_subpackets'
seal=R/S/'seal.json';val=R/E/'validation.json'
assert not seal.exists() and not val.exists(),'No repair/reseal or receipt overwrite allowed'
inv=json.loads((R/S/'inventory.json').read_text());owned=inv['owned_paths']
def sha(p):return hashlib.sha256((R/p).read_bytes()).hexdigest()
prospective={p:sha(p) for p in owned if p!=E+'/validation.json'}
command=[sys.executable,'-B',E+'/verify.py','--preseal']
t0=time.monotonic();p=subprocess.run(command,cwd=R,input=json.dumps(prospective),text=True,capture_output=True)
result=json.loads(p.stdout) if p.returncode==0 else None
receipt=dict(status='PASS' if p.returncode==0 and result['status']=='PASS' else 'FAIL',exit_code=p.returncode,command=command,cwd=str(R),elapsed_seconds=round(time.monotonic()-t0,2),stdout=p.stdout,stderr=p.stderr,result=result,scope='Read-only prevalidation receipt; no universal mathematics or acceptance certification.')
with val.open('x') as f:json.dump(receipt,f,indent=2);f.write('\n')
if receipt['status']!='PASS':
 print(json.dumps(receipt,indent=2));sys.exit(p.returncode or 1)
assert all(sha(p)==h for p,h in prospective.items()),'Bytes changed since prevalidation'
assert owned==sorted(set(owned))
sealed=dict(sha256={p:sha(p) for p in owned},scope='ONE seal following successful immutable prevalidation. No verifier repair/reseal capability.')
with seal.open('x') as f:json.dump(sealed,f,indent=2);f.write('\n')
print(json.dumps(dict(status='PASS',prevalidation_seconds=receipt['elapsed_seconds'],owned_files=len(owned),seal_sha256=sha(S+'/seal.json'),result=result),indent=2))
