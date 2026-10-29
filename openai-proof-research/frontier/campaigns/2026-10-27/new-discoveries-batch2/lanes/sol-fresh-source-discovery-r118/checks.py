"""Exact supporting exclusion checks; no discovery or formal certificate."""
from fractions import Fraction as Q
from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
count=0
for j in range(1,40):
 x=Q(j,100)
 # Direct public two-point concave sequence and an independently expanded deficit.
 k0=Q(2);k1=2*(x+(1+x));k2=3*(x*x+(1+x)**2)
 d=k1*k1-k0*k2
 assert d==4*x*x+4*x-2;count+=1
 if j<=36:assert d<0
x=Q(1,10)
assert (2*(2*x+1))**2-6*(x*x+(1+x)**2)==Q(-39,25)
for rec in json.loads((L/'source-lock.json').read_text()):
 p=L/rec['copy'];assert hashlib.sha256(p.read_bytes()).hexdigest()==rec['sha256'],str(p)
r={'exact_identity_checks':count,'explicit_public_midpoint_deficit':'-39/25','source_hash_checks':len(json.loads((L/'source-lock.json').read_text())),'status':'PASS; excluded public example only'}
(L/'check-results.json').write_text(json.dumps(r,indent=2));print(json.dumps(r))
