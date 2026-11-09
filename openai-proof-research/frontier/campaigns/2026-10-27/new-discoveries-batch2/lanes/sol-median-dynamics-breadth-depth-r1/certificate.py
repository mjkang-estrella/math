"""Exact Poisson-uniformization certificate; no floating point or third-party imports."""
from pathlib import Path
from fractions import Fraction as F
from math import factorial
import json
L=Path(__file__).resolve().parent
n=10;v=1;K=240
edges=[(2,1),(3,0),(3,1),(3,2),(4,3),(5,0),(5,2),(5,3),(6,1),(6,2),(6,4),(7,5),(8,0),(8,3),(8,4),(8,5),(9,1),(9,5),(9,7)]
neighbors=[[b if a==i else a for a,b in edges if i in (a,b)] for i in range(n)]
U=[]
for s in range(1<<n):
 row=[]
 for i in range(n):
  k=sum((s>>j)&1 for j in neighbors[i]);degree=len(neighbors[i]);old=(s>>i)&1
  new=1 if 2*k>degree else 0 if 2*k<degree else old
  row.append(s^((old^new)<<i))
 U.append(row)
f=[(s>>v)&1 for s in range(1<<n)]
g=[sum(f[z] for z in row)-n*f[s] for s,row in enumerate(U)]
assert set(g)<=set([-1,0,1])
w=[2**s.bit_count()*3**(n-s.bit_count()) for s in range(1<<n)]
assert sum(w)==5**n
coeff=[];S=F(0);E=F(0)
for k in range(K+1):
 c=sum(a*b for a,b in zip(w,g));coeff.append(c)
 S+=F(8**k,factorial(k))*c;E+=F(80**k,factorial(k))
 g=[sum(g[z] for z in row) for row in U]
tail=F(80**(K+1),factorial(K+1))/(1-F(80,K+2))
lower=(S-5**n*tail)/(5**n*(E+tail))
upper=(S+5**n*tail)/(5**n*E)
assert lower>F(18,10**6)
assert upper<F(19,10**6)
A=int(S*factorial(K));B=int(E*factorial(K));C=121*80**241;D=19521;W=5**10
assert F(C,D)==tail*factorial(K)
assert 10**6*(D*A-W*C)>18*W*(D*B+C)
assert 10**6*(D*A+W*C)<19*W*D*B
def rat(x):return dict(numerator=str(x.numerator),denominator=str(x.denominator))
out=dict(n=n,vertex=v,edges=edges,p='2/5',time='8',truncation=K,coefficients=[str(x) for x in coeff],S=rat(S),exponential_partial=rat(E),exponential_tail_bound=rat(tail),derivative_lower=rat(lower),derivative_upper=rat(upper),certified_interval=['18/1000000','19/1000000'],passed=True)
out['integer_certificate']={key:str(value) for key,value in dict(A=A,B=B,C=C,D=D,W=W).items()}
(L/'certificate-results.json').write_text(json.dumps(out,indent=2))
print('PASS: 18/1000000 < d/dt Pr(spin_1(t)=1) at p=2/5,t=8 < 19/1000000')
