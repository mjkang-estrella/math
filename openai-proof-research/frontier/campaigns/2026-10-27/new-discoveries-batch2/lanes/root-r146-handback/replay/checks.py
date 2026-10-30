import json,math
from fractions import Fraction as Q
from pathlib import Path
L=Path(__file__).resolve().parent
def cross(a,b,c):return (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
def hull(ps):
 ps=sorted(set(ps));low=[];up=[]
 for p in ps:
  while len(low)>1 and cross(low[-2],low[-1],p)<=0:low.pop()
  low.append(p)
 for p in reversed(ps):
  while len(up)>1 and cross(up[-2],up[-1],p)<=0:up.pop()
  up.append(p)
 return low[:-1]+up[:-1]
def area(ps):return abs(sum(p[0]*q[1]-p[1]*q[0] for p,q in zip(ps,ps[1:]+ps[:1])))/2
def add(a,b):return hull([(x[0]+y[0],x[1]+y[1]) for x in a for y in b])
def mixed(a,b):return (area(add(a,b))-area(a)-area(b))/2
rows=[]
for k in range(1,15):
 pts=[(Q(1),Q(0)),(Q(0),Q(1)),(Q(1,3),Q(k,10)),(Q(k,10),Q(1,4))]
 C=hull(pts+[(-x,-y) for x,y in pts]);A=area(C);S=[(Q(-1),Q(0)),(Q(1),Q(0))];M=mixed(C,S)
 assert M<=A
 for u in [Q(1,7),Q(1,3),Q(2,3),Q(6,7)]:
  Cu=hull([(u*x,u*y) for x,y in C]+S)
  assert area(Cu)<=u*u*A+u*(1-u)*M
  for v in [Q(0),u/3,u]:
   Cv=hull([(v*x,v*y) for x,y in C]+S)
   V=mixed(Cu,Cv);bound=u*v*A+(u-u*v)*M
   assert V<=bound
   rows.append(dict(k=k,u=str(u),v=str(v),area=str(A),M=str(M),mixed=str(V),bound=str(bound)))
# Exact p=2 scalar support identity via elementary antiderivative:
# F''=sqrt(2)/(1+u^2)^(3/2); identity checked by midpoint quadrature only.
numeric=[]
N=8000
for t in [0,.1,.4,.8,1]:
 s=sum(max(abs(t),(i+.5)/N)*math.sqrt(2)/(1+((i+.5)/N)**2)**1.5/N for i in range(N))
 err=abs(1+s-math.sqrt(2*(1+t*t)))
 assert err<1e-7
 numeric.append(dict(t=t,error=err))
(L/'checks.json').write_text(json.dumps(dict(status='PASS',exact_cases=len(rows),rows=rows,scalar_diagnostics=numeric,limits='168 rational finite polygon/mixed-area cases and 5 p=2 quadratures; no general-proof or novelty certificate.'),indent=2)+'\n')
print('PASS',len(rows),'exact mixed-area cases; 5 scalar quadratures')
