import resource
resource.setrlimit(resource.RLIMIT_AS,(480*1024**2,480*1024**2))
from collections import defaultdict
from fractions import Fraction as Q
from math import comb,factorial
from pathlib import Path
import json
# R=Z[a,b,x,w]/(w^2=1+x^2), key=(a,b,x,w), w=0,1.
def clean(p):return {k:c for k,c in p.items() if c}
def add(*ps):
 q=defaultdict(int)
 for p in ps:
  for k,c in p.items():q[k]+=c
 return clean(q)
def scale(p,c):return clean({k:c*v for k,v in p.items()})
def mul(p,q):
 out=defaultdict(int)
 for (a,b,x,w),c in p.items():
  for (A,B,X,W),C in q.items():
   if w+W<2:out[a+A,b+B,x+X,w+W]+=c*C
   else:
    out[a+A,b+B,x+X,0]+=c*C
    out[a+A,b+B,x+X+2,0]+=c*C
 return clean(out)
def deriv(p):
 out=defaultdict(int)
 for (a,b,x,w),c in p.items():
  if x:
   out[a,b,x-1,w]-=x*c;out[a,b,x+1,w]-=x*c
  if w:out[a,b,x+1,w]-=c
 return clean(out)
def v2(c):
 c=Q(c)
 if not c:return 99999
 def v(n):n=abs(n);return (n&-n).bit_length()-1
 return v(c.numerator)-v(c.denominator)
P={(1,0,0,0):1,(1,0,2,0):1,(0,1,1,1):1}
h=[{},P]
for n in range(1,15):
 h.append(add(scale(deriv(h[n]),-1),*[scale(mul(h[j],h[n-j]),-1) for j in range(1,n)]))
rows=[]
fail=[]
for r in range(1,9):
 n=2*r-1
 for d in range(1,r+1):
  q={k:c for k,c in h[n].items() if k[0]+k[1]==d and k[3]==1}
  bound=(d-1).bit_count()
  low=min(map(v2,q.values()),default=99999)
  rows.append({'r':r,'d':d,'w_odd_content':low,'candidate_bound':bound})
  if low<bound:fail.append({'r':r,'d':d,'terms':[[list(k),str(c)] for k,c in q.items() if v2(c)<bound]})
# Independent free differential polynomial recurrence: P=A+B and derivation shifts jet indices.
def fm(p,q):
 out=defaultdict(int)
 for k,c in p.items():
  for K,C in q.items():out[tuple(sorted(k+K))]+=c*C
 return clean(out)
def fd(p):
 out=defaultdict(int)
 for k,c in p.items():
  for j,(a,i) in enumerate(k):out[tuple(sorted(k[:j]+((a,i+1),)+k[j+1:]))]+=c
 return clean(out)
f=[{},{((0,0),):1,((1,0),):1}]
for n in range(1,9):f.append(add(scale(fd(f[n]),-1),*[scale(fm(f[j],f[n-j]),-1) for j in range(1,n)]))
free=[]
for n in range(1,10,2):
 for d in range(1,(n+1)//2+1):
  q={k:c for k,c in f[n].items() if len(k)==d and sum(a for a,i in k)%2}
  low=min(map(v2,q.values()),default=99999)
  if low<(d-1).bit_count():free.append({'n':n,'d':d,'min':low,'bound':(d-1).bit_count(),'witness':next([list(k),c] for k,c in q.items() if v2(c)<(d-1).bit_count())})
out={'rows':rows,'specific_failures':fail,'free_differential_failures':free,'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss}
Path(__file__).with_name('explore.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps(out,indent=2))
# Full integral bidegree filtration, all coefficients in the bounded diagnostic.
for n in range(1,16):
 for (i,j,x,w),c in h[n].items():
  assert i+j and v2(c)>=i.bit_count()+j.bit_count()-1
  assert w==j%2 and (x+w)%2==(n+1)%2
# Downward primitive in midpoint coordinates; independent from t-Laurent integration.
def prim_mid(p):
 groups=defaultdict(dict)
 for (a,b,x,w),c in p.items():groups[a,b,w][x]=Q(c)
 out={}
 for (a,b,w),f in groups.items():
  if not w:
   # Divide the even polynomial by 1+x^2.
   q={}
   while f and max(f)>=2:
    k=max(f);c=f.pop(k);q[k-2]=c
    f[k-2]=f.get(k-2,Q())-c
    if not f[k-2]:del f[k-2]
   assert not f
   for k,c in q.items():
    assert not k%2
    out[a,b,k+1,0]=-c/(k+1)
  else:
   assert all(k%2 for k in f)
   Fnext=Q()
   for k in range((max(f)-1)//2,-1,-1):
    Fnext=(-f.get(2*k+1,Q())-2*(k+1)*Fnext)/(2*k+1)
    if Fnext:out[a,b,2*k,1]=Fnext
 assert deriv(out)==p
 return out

def ab_to_uv(p):
 out=defaultdict(Q)
 for (i,j),c in p.items():
  for k in range(i+1):
   for l in range(j+1):out[k+l,i+j-k-l]+=c*comb(i,k)*comb(j,l)*(-1)**(j-l)
 return clean(out)
normalized_J={}
for r in range(1,9):
 n=2*r-1;pr=prim_mid(h[n]);J={}
 for (a,b,x,w),c in pr.items():
  if w:
   assert v2(c)>=(a+b-1).bit_count()
  if x==0:
   assert w==1
   J[a,b]=c*2**(n-a-b)
 normalized_J[n]=ab_to_uv(J)

# Independent original t-Laurent recurrence, with no midpoint-coordinate operations.
def tm(p,q):
 out=defaultdict(int)
 for (a,b,k),c in p.items():
  for (A,B,K),C in q.items():out[a+A,b+B,k+K]+=c*C
 return clean(out)
def td(p):
 out=defaultdict(int)
 for (a,b,k),c in p.items():out[a,b,k-1]-=k*c;out[a,b,k+1]-=k*c
 return clean(out)
def tprim(p):
 groups=defaultdict(dict);out={}
 for (a,b,k),c in p.items():groups[a,b][k]=c
 for (a,b),f in groups.items():
  low=min(f);q={}
  while f and max(f)>=low+2:
   k=max(f);c=f.pop(k);q[k-2]=c
   f[k-2]=f.get(k-2,0)-c
   if not f[k-2]:del f[k-2]
  assert not f
  for k,c in q.items():
   assert k%2==0
   out[a,b,k+1]=-Q(c,k+1)
 assert td(out)==p
 return out
V={(1,0,0):1,(1,0,2):1,(0,1,0):1,(0,1,-2):1}
s=[{},V]
for n in range(1,9):s.append(add(scale(td(s[n]),-1),*[scale(tm(s[j],s[n-j]),-1) for j in range(1,n)]))
for n in range(1,10,2):
 J=defaultdict(Q)
 for (a,b,k),c in tprim(s[n]).items():J[a,b]+=c
 assert clean(J)==normalized_J[n]

# A third pipeline: literal Definition 2.1, independent of both differential recurrences.
import sympy as sp
from sympy.functions.combinatorial.numbers import stirling
u,v=sp.symbols('u v',real=True)
fall=lambda x,k:sp.prod(x-j*(j+1) for j in range(k))
C=[sp.expand(sum(comb(k,j)*fall(u,j)*fall(v,k-j)*(1+sp.I)**j*(1-sp.I)**(k-j) for j in range(k+1))) for k in range(10)]
A=[sp.Integer(1)]+[sp.expand(sum(2**(n-k)*(factorial(n)//factorial(k))*stirling(n,k,kind=2)*C[k] for k in range(1,n+1))) for n in range(1,10)]
B=[sp.Integer(0)]
for n in range(1,10):
 B.append(sp.expand(A[n]-sum(comb(n-1,j-1)*B[j]*A[n-j] for j in range(1,n))))
 if n%2:
  r=(n+1)//2
  rhs=sum(sp.Rational(c.numerator,c.denominator)*u**a*v**b for (a,b),c in normalized_J[n].items())*((-1)**r*factorial(n))
  assert sp.expand(sp.im(B[n])-rhs)==0
 else:assert sp.im(B[n])==0

# Symbolic proof identities checked without numerical fitting.
x,w,aa,bb=sp.symbols('x w a b')
# Coordinate V=2P follows after w^2-x^2=1, t=w+x, t^-1=w-x.
expr=u*(1+(w+x)**2)+v*(1+(w-x)**2)-2*((u+v)*w**2+(u-v)*w*x)
assert sp.rem(sp.Poly(expr,w),sp.Poly(w*w-x*x-1,w)).as_expr()==0
for k in range(5):
 raw=-w*w*sp.diff(w*x**(2*k),x)-w*x*sp.diff(w*x**(2*k),w)
 target=-w*x*((2*k+1)*x**(2*k)+(2*k*x**(2*k-2) if k else 0))
 assert sp.rem(sp.Poly(sp.expand(raw-target),w),sp.Poly(w*w-x*x-1,w)).as_expr()==0
# Fixed tiny adversarial checks of weight inequalities and odd-unit inverse.
for i in range(16):
 for j in range(16):
  if j%2:assert i.bit_count()+j.bit_count()-1 >= (i+j-1).bit_count()
  assert (i+j).bit_count()<=i.bit_count()+j.bit_count()
assert Q(1)+Q(1,3)==Q(4,3)
assert sum((Q(comb(3,j),2*j+3) for j in range(4)),Q())==Q(464,315)
# Report exactly what executed; not an all-order certificate.
out.update({'status':'PASS finite diagnostic; ordinary all-order proof is PROOF.md; no full Lean endpoint',
 'integral_bidegree_filtration_n_max':15,'normalized_primitive_r_max':8,
 'independent_original_t_recurrence_n_max':9,'literal_source_cumulant_n_max':9,
 'coordinate_and_primitive_identities':True,
 'max_rss_kib':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss})
Path(__file__).with_name('checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='rows'},indent=2))
