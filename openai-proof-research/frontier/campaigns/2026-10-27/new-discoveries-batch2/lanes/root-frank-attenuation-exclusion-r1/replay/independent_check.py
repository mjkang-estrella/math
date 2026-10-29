"""Independent integer fixed-point interval checker. No candidate code imported.
Analytic existence argument is separate; this checks the finite witness only.
"""
import json,math
from fractions import Fraction as Q
from pathlib import Path
L=Path(__file__).resolve().parent
D=10**24
def exact(x):
 x=Q(x)*D;return (x.numerator//x.denominator,-((-x.numerator)//x.denominator))
def add(a,b):return a[0]+b[0],a[1]+b[1]
def neg(a):return -a[1],-a[0]
def sub(a,b):return add(a,neg(b))
def mul(a,b):
 v=[x*y for x in a for y in b];return min(v)//D,-(-max(v)//D)
def div(a,b):
 assert b[0]>0
 vals=[Q(x*D,y) for x in a for y in b];lo=min(vals);hi=max(vals)
 return lo.numerator//lo.denominator,-(-hi.numerator//hi.denominator)
one=exact(1)
def scale(a,q):return mul(a,exact(q))
def exp8(x):
 term=one;total=one
 for j in range(1,101):term=scale(term,x/j);total=add(total,term)
 # x<=8 and ratio of all subsequent terms <=8/102<1/2.
 return add(total,(0,exact(Q(2*8**101,math.factorial(101)))[1]))
def lnpoint(x):
 k=0
 while x<1:x*=2;k-=1
 while x>2:x/=2;k+=1
 return add(lnunit(exact(x)),scale(log2,k))
def lnunit(x):
 z=div(sub(x,one),add(x,one));z2=mul(z,z);term=z;out=(0,0)
 for j in range(90):out=add(out,scale(term,Q(2,2*j+1)));term=mul(term,z2)
 # z<=1/3: tail 2*z^181/(181*(1-z²)) < 3/3^181.
 return add(out,(0,exact(Q(3,3**181))[1]))
log2=lnunit(exact(2))
def log(a):return lnpoint(Q(a[0],D))[0],lnpoint(Q(a[1],D))[1]
ts=[Q(t) for t in json.loads((L/'inputs/certificate.json').read_text())['thresholds']]
assert len(ts)==19 and all(a<b for a,b in zip([Q(0)]+ts,ts+[Q(1)]))
e={t:div(one,exp8(8*t)) for t in ts};q=div(one,exp8(Q(8)))
cov=(0,0);variance=Q(0)
# X=1+sum 1_{U>t}; Cov indicators = C(t,s)-ts.
for t in ts:
 for s in ts:
  a=sub(one,div(mul(sub(one,e[t]),sub(one,e[s])),sub(one,q)))
  c=scale(log(a),Q(-1,8));cov=add(cov,sub(c,exact(t*s)))
  variance+=min(t,s)-t*s
ordinal=div(cov,exact(variance))
# J_j=integral_0^8 t^j/(exp(t)-1) dt; positive exponential series.
# K=1000 tails <=1/K and 1/K²; intentionally coarser than supplied certificate.
j1=(0,0);j2=(0,0);qk=q;K=1000
for k in range(1,K+1):
 j1=add(j1,scale(sub(one,scale(qk,1+8*k)),Q(1,k*k)))
 j2=add(j2,scale(sub(exact(2),scale(qk,2+16*k+64*k*k)),Q(1,k**3)))
 qk=mul(qk,q)
j1=add(j1,(0,exact(Q(1,K))[1]));j2=add(j2,(0,exact(Q(1,K*K))[1]))
latent=add(sub(one,scale(j1,Q(3,16))),scale(j2,Q(3,64)))
assert ordinal[0]>exact(Q(201,250))[1]>latent[1]
# Independent rational endpoint obstruction, not a numerical nonaffineness test.
assert sum((Q(8**j,math.factorial(j)) for j in range(8)),Q(0))>1000
assert Q(1001,1998)<Q(3,4)
out=dict(pass_all=True,categories=20,thresholds=[str(t) for t in ts],
 ordinal=[str(Q(x,D)) for x in ordinal],latent=[str(Q(x,D)) for x in latent],
 separator='201/250',precision_denominator=str(D),tail_cutoff=K,
 methods='independent integer interval operations; exp 100 terms; range-reduced log 90 terms; positive-series integrals',
 limitation='finite rational certificate only; universal/existential analytic proof reviewed by hand')
(L/'independent-check.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out))
