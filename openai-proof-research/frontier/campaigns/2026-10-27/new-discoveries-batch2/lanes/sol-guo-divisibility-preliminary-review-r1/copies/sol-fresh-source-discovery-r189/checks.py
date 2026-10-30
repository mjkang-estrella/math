"""Exact bounded diagnostics only; not an all-order proof. Run through assigned guard."""
import math,json
from fractions import Fraction as F
def C(n,k):return math.comb(n,k) if 0<=k<=n else 0
def df(l):return math.prod(range(1,2*l,2))
def coeff(r,k):
 a=[1]
 for j in range(r):
  b=[0]*(len(a)+1)
  for t,v in enumerate(a):b[t]+=(2*k+2*t+1)**2*v;b[t+1]+=v
  a=b
 return a
def raw(l,n,k):return C(2*k,k)**2*sum((2*m+1)**(2*l-1)*C(m+k,2*k) for m in range(k,n))
def terms(l,n,k):
 out=[]
 for t,a in enumerate(coeff(l-1,k)):
  q=k+t
  out.append(F(a*4**t*math.factorial(2*k)*math.factorial(q)**2,math.factorial(k)**4*(q+1))*C(n-1,q)*C(n+q,q))
 return out
tested=identities=0; failures=[];termfail=None;coefffail=None;nofactor=None
for l in range(1,11):
 for n in range(1,81):
  for k in range(n):
   s=raw(l,n,k); tested+=1
   if df(l)*s%(n*n):failures.append([l,n,k])
   if nofactor is None and s%(n*n):nofactor=[l,n,k,s%(n*n)]
   if n<=30 and l<=7:
    ts=terms(l,n,k); assert sum(ts)==F(s,n*n); identities+=1
    if termfail is None:
     for t,x in enumerate(ts):
      if (df(l)*x).denominator!=1:termfail=[l,n,k,t,str(df(l)*x)];break
for l in range(1,10):
 for k in range(40):
  for t,a in enumerate(coeff(l-1,k)):
   q=k+t;x=F(df(l)*a*4**t*math.factorial(2*k)*math.factorial(q)**2,math.factorial(k)**4*(q+1))
   if x.denominator!=1 and coefffail is None:coefffail=[l,k,t,str(x)]
lemma_tests=0
for k in range(501):
 for t in range(51):
  assert (4**t*df(t+1)*C(2*k,k))%(k+t+1)==0
  lemma_tests+=1
print(json.dumps(dict(source_tests=tested,source_failures=failures,expansion_identity_tests=identities,termwise_integrality_falsifier=termfail,coefficient_integrality_falsifier=coefffail,omit_double_factorial_falsifier=nofactor,denominator_lemma_tests=lemma_tests,scope='1<=l<=10,1<=n<=80,0<=k<n; identity l<=7,n<=30; denominator lemma 0<=k<=500,0<=t<=50; finite only'),indent=2))
