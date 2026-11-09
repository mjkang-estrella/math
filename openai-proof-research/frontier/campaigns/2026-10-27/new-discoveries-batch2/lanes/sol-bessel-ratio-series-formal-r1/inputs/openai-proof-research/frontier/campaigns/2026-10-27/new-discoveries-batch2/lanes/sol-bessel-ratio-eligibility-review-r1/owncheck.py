from fractions import Fraction as Q
from pathlib import Path
import json
O=Path(__file__).parent
# Independent interval enclosure of the defining positive series and weighted derivative.
# C*x^nu is suppressed; remaining W has its sign unchanged.
def bounds(nu,a,x,N=100):
 z=(a*x)**2/4; t=Q(1); F=Q(0); E=Q(0)
 for k in range(N):
  F+=t; E+=(nu+2*k)*t
  t*=z/((k+1)*(k+nu+1))
 r=z/((N+1)*(N+nu+1)); assert 0<=r<1
 T=t/(1-r)
 # weighted remainder <= t*((nu+2N)/(1-r)+2r/(1-r)^2)
 U=t*((nu+2*N)/(1-r)+2*r/(1-r)**2)
 return (F,F+T),(E,E+U)
def mul(A,B):
 v=[a*b for a in A for b in B];return min(v),max(v)
def sign(u,v,a,b,x):
 F,E=bounds(u,a,x);G,H=bounds(v,b,x)
 P=mul(E,G);R=mul(F,H);L=P[0]-R[1];U=P[1]-R[0]
 return '+' if L>0 else '-' if U<0 else 'undetermined'
rows=[]
for u,v,a,b,x,want in [
 ('-1/4','-3/4',1,1,'1/10','+'),('-1/4','-3/4',1,1,20,'-'),
 ('1/2','-1/2',1,1,20,'+'),('-3/4','-3/4',1,2,'1/10','-'),
 ('-3/4','-3/4',1,2,20,'-'),('3/2','1/4',1,2,'1/10','+'),('3/2','1/4',1,2,20,'-'),
 ('3/2','1/4',1,1,20,'+')]:
 got=sign(*map(Q,[u,v,a,b,x]));assert got==want
 rows.append(dict(u=u,v=v,a=a,b=b,x=x,expected=want,certified=got))
# An exact falsifier of omitting initial positivity in a generic one-turn lemma:
# W=1-(x-2)^2, W'=4-2x, positive f/g realization R=10+integral W on (0,4).
# W has two interior roots 1,3 despite W' changing + to - only once.
assert 1-(Q(1)-2)**2==0 and 1-(Q(3)-2)**2==0
(O/'ownchecks.json').write_text(json.dumps({'method':'exact rational series with infinite geometric weighted tail; N=100, independent sign enclosures, not universal proof','cases':rows,'generic_missing_endpoint_counterexample':'W=1-(x-2)^2 on (0,4): zeros 1 and 3; Wprime=4-2x','status':'PASS'},indent=2))
print('PASS: 8 infinite-series W-sign certificates, including negative orders/sums and equal scales; missing-endpoint counterexample exact')
