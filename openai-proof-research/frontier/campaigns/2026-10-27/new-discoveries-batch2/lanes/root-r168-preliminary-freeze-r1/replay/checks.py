from fractions import Fraction as F
from pathlib import Path
import json,hashlib
L=Path(__file__).resolve().parent
r,s=100000,225985
# Exact total-mass ratio A(1)/B(1) = 5^r 2^(s-r) / 3^s.
u=5**r * 2**(s-r);v=3**s
assert v<u<2*v
muA=F(9*r,5)+F(s,2);muB=F(3*r,2)+F(2*s,3)
varA=F(33*r,50)+F(s,4);varB=F(3*r,4)+F(2*s,9)
centers=[292993,296825,300657]; windows=[(c-1000,c+1000) for c in centers]
assert muA<muB and varA<126000 and varB<126000
assert abs(muA-centers[0])<1 and abs(muB-centers[2])<1
assert windows[1][0]-muA>2800 and muB-windows[1][1]>2800
assert F(126000,2800**2)<F(17,1000)
assert F(126000,1000**2)==F(126,1000)
assert F(1)-F(126,1000)-F(1,100)>F(86,100)
assert F(17,1000)*3<F(86,100)
assert F(2,5)**6<F(1,100) and F(2,3)**12<F(1,100)
# Analytic finite certificate for the total-mass ratio, independent of big powers.
def logbounds(t):
 S=2*sum(t**(2*j+1)/F(2*j+1) for j in range(20))
 return S,S+2*t**41/(41*(1-t*t))
a,b=logbounds(F(3,7));c,d=logbounds(F(1,5))
assert F(9162907318741,10**13)<a<b<F(9162907318742,10**13)
assert F(4054651081081,10**13)<c<d<F(4054651081082,10**13)
assert 0<r*a-s*d<r*b-s*c<F(1,10)
# Independent tiny graph enumerator controls join/corona formula, not large witness proof.
def mul(a,b):
 c=[0]*(len(a)+len(b)-1)
 for i,x in enumerate(a):
  for j,y in enumerate(b):c[i+j]+=x*y
 return c
def power(a,k):
 c=[1]
 for _ in range(k):c=mul(c,a)
 return c
def formula(r,s,p):
 a=mul(power([1,p],2*r+s),power([1,p+3],r))
 b=mul(power([1,p],3*r),power([1,p+1],s));c=power([1,p],3*r+s)
 return [x+y-z for x,y,z in zip(a,b,c)]
def enum(r,s,p):
 n=3*r+s;N=n*(p+1);edges=[]
 for i in range(3*r):
  for j in range(i+1,3*r):
   if i//3==j//3:edges.append((i,j))
 for i in range(3*r):
  for j in range(3*r,n):edges.append((i,j))
 for i in range(n):
  block=[i]+list(range(n+i*p,n+(i+1)*p))
  edges.extend((x,y) for ix,x in enumerate(block) for y in block[ix+1:])
 masks=[(1<<i)|(1<<j) for i,j in edges];out=[0]*(n+1)
 for mask in range(1<<N):
  if all(mask&e!=e for e in masks):out[mask.bit_count()]+=1
 return out
controls=[]
for rr,ss,pp in [(1,1,1),(1,2,1),(1,1,2)]:
 a=enum(rr,ss,pp);assert a==formula(rr,ss,pp);controls.append(dict(r=rr,s=ss,p=pp,coefficients=a))
result=dict(status='PASS',r=r,s=s,base_vertices=3*r+s,corona_vertices=2*(3*r+s),mass_ratio_between=[1,2],muA=str(muA),muB=str(muB),varA=str(varA),varB=str(varB),windows=windows,controls=controls,large_coefficients_enumerated=False)
(L/'checks.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
