"""Independent verifier; does not import the diagnostic implementation."""
import json,hashlib,datetime,itertools as it,math
from pathlib import Path
L=Path(__file__).resolve().parent
j=json.loads((L/'finalmanifest.json').read_text());count=0
for r in j['records']:
 b=(L/r['path']).read_bytes();assert len(b)==r['bytes'];assert hashlib.sha256(b).hexdigest()==r['sha256'];count+=1
f=json.loads((L/'scientific-freeze.json').read_text())
for r in f['records']+f['administrative_snapshots']:
 b=(L/r['path']).read_bytes();assert hashlib.sha256(b).hexdigest()==r['sha256']
expected={r['path'] for r in j['records']}|{'finalmanifest.json','manifest-verification.json','verification-guard.json'}
assert not {str(p.relative_to(L)) for p in L.rglob('*') if p.is_file()}-expected
# Independent exact expansion of excluded identity, at all integer coefficient positions.
from fractions import Fraction
poly=[(1 if k==4 else 0)+(-1)**k*math.comb(4,k)+(1 if k==0 else 0) for k in range(5)]
assert poly==[2,-4,6,-4,2]
assert poly==[2*sum([1,-1,1][i]*[1,-1,1][k-i] for i in range(3) if 0<=k-i<3) for k in range(5)]
# Verify explicit cubic obstruction: neither term contains any antidiagonal cell generator.
P={(0,0),(0,2),(1,1)}
lm=[{(x,y+1),(x+1,y)} for x,y in P]
terms=[{(0,2),(1,3),(2,1)},{(0,3),(1,1),(2,2)}]
assert all(not m<=t for m in lm for t in terms)
# Small-model independent Hilbert value via complete-intersection formula.
# This is a diagnostic cross-check only; ordinary notes prove the method obstruction.
ds=json.loads((L/'diagnostics.json').read_text())[0]['diagnostic'];assert ds['H']==[sum((-1)**j*math.comb(3,j)*math.comb(9+k-2*j,k-2*j) for j in range(4) if k>=2*j) for k in range(5)]
out=dict(utc=datetime.datetime.now(datetime.timezone.utc).isoformat(),manifest_sha256=hashlib.sha256((L/'finalmanifest.json').read_bytes()).hexdigest(),manifest_entries_verified=count,scientific_entries_verified=len(f['records']),administrative_snapshots_verified=len(f['administrative_snapshots']),extra_files=0,identity_and_method_objection='PASS',independence='Separately authored verifier, no checks.py import; no external independent agent review claimed',status='PASS')
(L/'manifest-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
