"""Exact finite certificate checks; no numerical search or universal numerical inference."""
from pathlib import Path
from math import comb
import json, hashlib
L=Path(__file__).resolve().parent
P={0:786520,56:-3433500,109:5698350,162:-14554225,165:10918530,218:584325}
# Formal power series division by (1-t)^4. Since degree(P)=218,
# these are all 215 coefficients of the polynomial quotient.
q=[sum(a*comb(k-j+3,3) for j,a in P.items() if j<=k) for k in range(215)]
assert len(q)==215 and min(q)>0
product=[0]*219
for k,a in enumerate(q):
 for j,c in enumerate([1,-4,6,-4,1]):product[k+j]+=a*c
assert product==[P.get(k,0) for k in range(219)]
# Independent sparse multiplication checks the derivative numerator without
# relying on polynomial division or a symbolic algebra package.
def mul(a,b):
 d={}
 for i,x in a.items():
  for j,y in b.items():d[i+j]=d.get(i+j,0)+x*y
 return d
numerator=mul({109:105,0:4},{56:1962,109:105,0:3710})
numerator={k:53*v for k,v in numerator.items()}
for k,v in mul({0:18,53:35},{0:18,53:35}).items():numerator[k+56]=numerator.get(k+56,0)-109**2*v
assert {k:v for k,v in numerator.items() if v}==P
cert=dict(sparse_numerator=P,quotient_coefficients_low_to_high=q,degree=214,minimum_coefficient=min(q),all_215_strictly_positive=True,identity='P(t)=(t-1)^4 Q(t)')
data=(json.dumps(cert,indent=2)+'\n').encode()
if (L/'certificate.json').exists():assert (L/'certificate.json').read_bytes()==data
else:(L/'certificate.json').write_bytes(data)
print(json.dumps(dict(status='PASS',quotient_coefficients=215,reconstructed_coefficients=219,sparse_derivative_identity=True,certificate_sha256=hashlib.sha256(data).hexdigest(),scope='Exact finite algebra certificate only; calculus and source bridge are in PROOF.md.')))
