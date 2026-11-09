"""Independent integer arithmetic; coefficients in ascending order. No CAS."""
from pathlib import Path
import json,sys
L=Path(__file__).resolve().parents[1]
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,u in enumerate(a):
  for j,v in enumerate(b):c[i+j]+=u*v
 return c
def deriv(a):return [i*a[i] for i in range(1,len(a))]
def ev(a,x):
 y=0
 for z in a[::-1]:y=y*x+z
 return y
P=[108312103,304200,177450,-600,-13200,0,50]
J=[127901873749,-1479679536,-57294664659,-79953900,525944015,1064700,414050,-900,-13200,0,25]
g=[300]
roots=[-13,-2,-1,3,13]
for r in roots:g=mul(g,[-r,1])
assert deriv(P)==g
a=mul(P,deriv(deriv(P)));b=mul(deriv(P),deriv(P))
assert [4*u-3*v for u,v in zip(a,b)]==[1200*z for z in J]
critical={str(r):ev(P,r) for r in roots};assert min(critical.values())==3
intervals=[[-20,-19],[-14,-13],[-13,-12],[-2,-1],[1,2],[12,13],[14,15],[19,20]]
signs=[{'interval':v,'values':[ev(J,x) for x in v]} for v in intervals]
assert all(t['values'][0]*t['values'][1]<0 for t in signs)
assert all(intervals[i][1]<=intervals[i+1][0] for i in range(7))
result={'derivative_factor_identity':True,'numerator_identity':True,'critical_values':critical,'sign_certificates':signs,'distinct_real_roots_at_least':8,'scope':'Exact finite algebra and signs. IVT and coercive critical-point argument are ordinary proof in PROOF.md.'}
if '--verify' not in sys.argv:(L/'proof-check.json').write_text(json.dumps(result,indent=2)+'\n')
else:assert json.loads((L/'proof-check.json').read_text())==result
print(json.dumps(result))
