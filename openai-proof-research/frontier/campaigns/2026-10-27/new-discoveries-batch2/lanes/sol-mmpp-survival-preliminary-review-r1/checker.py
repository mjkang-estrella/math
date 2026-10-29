from fractions import Fraction as F
from math import factorial
from pathlib import Path
import json
b=Path(__file__).resolve().parent
a=[9,8,7,6,5,4,3,4,5,6,7,8];n=12;t=F(48,5);w=[F(6-x,72) for x in a];L=sum(map(abs,w))
Q=[[F((j==(i+1)%n)-(i==j)) for j in range(n)] for i in range(n)]
C=[[Q[i][j]-(F(a[i],60) if i==j else 0) for j in range(n)] for i in range(n)]
pi=[F(1,12)]*n;alpha=[F(x,72) for x in a]
def row(v,M): return [sum(v[i]*M[i][j] for i in range(n)) for j in range(n)]
assert row(pi,Q)==[0]*n and sum(alpha)==1 and sum(F(x,720) for x in a)==F(1,10)
assert row(pi,C)==[-F(x,720) for x in a]
# Direct ROW propagation, dense explicit rational matrix, includes terms 0..160.
v=w[:];U=F(0)
for k in range(161):
 U+=sum(v)*t**k/factorial(k);v=row(v,C)
z=t*max(sum(map(abs,r)) for r in C)
E=L*z**161/F(factorial(161))/(1-z/162)
assert z==F(516,25) and U+E < -F(1,25000)
r=F(23,20);s=r*t
P=[[(i==j)+C[i][j]/r for j in range(n)] for i in range(n)]
assert all(x>=0 for rr in P for x in rr) and all(sum(rr)<=1 for rr in P)
v=w[:];S=F(0)
for k in range(81):
 S+=sum(v)*s**k/factorial(k);v=row(v,P)
B=L*s**81/F(factorial(81))/(1-s/82)
assert S < -2 and B < F(1,100)
# Invert -C from scratch and verify embedded chain and Palm invariance exactly.
M=[[-C[i][j] for j in range(n)]+[F(i==j) for j in range(n)] for i in range(n)]
for j in range(n):
 h=M[j][j];assert h;M[j]=[x/h for x in M[j]]
 for i in range(n):
  if i!=j:
   h=M[i][j];M[i]=[x-h*y for x,y in zip(M[i],M[j])]
Inv=[rr[n:] for rr in M];K=[[Inv[i][j]*F(a[j],60) for j in range(n)] for i in range(n)]
assert all(x>0 for rr in K for x in rr) and all(sum(rr)==1 for rr in K) and row(alpha,K)==alpha
mean=sum(row(alpha,Inv));m2=2*sum(row(row(alpha,Inv),Inv));scv=m2/mean**2-1
assert mean==10 and scv>1
# The source's four-state hazard example: not independently a survival crossing at this t.
res={'L':str(L),'z':str(z),'S80':str(S),'B80':str(B),'U160':str(U),'E160':str(E),'strict_bound':'U160+E160 < -1/25000','survival_gap_approx_for_orientation_only':float(U),'uniformization_S_approx':float(S),'tail80_approx':float(B),'tail160_approx':float(E),'mean_event':str(mean),'SCV':str(scv),'embedded_positive_stochastic_stationary':True,'all_assertions_passed':True}
(b/'independent-check.json').write_text(json.dumps(res,indent=2));print({k:v for k,v in res.items() if k not in ['S80','B80','U160','E160','SCV']})
