import json,math,itertools,random,time
from fractions import Fraction as F
from pathlib import Path
L=Path(__file__).resolve().parent
def exact(a,w):
 s=e=F(0)
 for i,j,k,l in itertools.product(range(len(a)),repeat=4):
  t=w[i]*w[j]*w[k]*w[l];d=a[i]+a[j]+a[k]-2*a[l]
  if d<0:s+=t
  elif d==0:e+=t
 return s,e,s/(1-e)
def dyadic_formula(p,w):
 s=sum(w);n=len(w)
 one=sum(w[k]*(s*s-sum(w[k:])**2) for k in range(n))
 positive=w[0]**3*sum(w[2:])+3*w[0]**2*sum(w[j]*sum(w[j+2:]) for j in range(1,n))
 equalpos=w[0]**3*(w[1] if n>1 else 0)+3*w[0]**2*sum(w[j]*w[j+1] for j in range(1,n-1))
 return p**3*s+3*p*p*s*s+3*p*one+positive,p**4+3*p*sum(t**3 for t in w)+equalpos
out={'finite_checks_are_not_proof':True,'exact':[]}
for n in range(2,9):
 p=F(47,100);w=[(1-p)/n]*n;a=[F(0)]+[1-F(1,2**i) for i in range(1,n+1)]
 s,e,q=exact(a,[p]+w);ss,ee=dyadic_formula(p,w);assert (s,e)==(ss,ee)
 out['exact'].append(dict(N=n,strict=str(s),equality=str(e),renewal_ratio=str(q),decimal=float(q)))
for n in [1,2,3,4,8,16,32,64,128,156,256,512,1024]:
 p=F(474346,1000000);w=[(1-p)/n]*n;s,e=dyadic_formula(p,w)
 out['exact'].append(dict(N=n,formula_only=True,renewal_ratio=str(s/(1-e)),decimal=float(s/(1-e))))

reference=json.loads((L.parent/'sol-fresh-source-discovery-r140/checks.json').read_text())
assert out['exact']==reference['exact']
(L/'exact-replay.json').write_text(json.dumps(out,indent=2)+'\n')
print('PASS',len(out['exact']),'exact records; floating search deliberately not repeated')
