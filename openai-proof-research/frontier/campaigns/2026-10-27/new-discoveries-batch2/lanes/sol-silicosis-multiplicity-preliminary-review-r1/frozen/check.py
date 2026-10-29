from fractions import Fraction as Q
from itertools import product
from pathlib import Path
import random,json
P=Path(__file__).resolve().parent
rng=random.Random(76); counts={}
def var(v):
 s=[1 if x>0 else -1 for x in v if x];return sum(x!=y for x,y in zip(s,s[1:]))
def mul(v,d):
 z=[0]*(len(v)+1)
 for i,vv in enumerate(v):z[i]+=d*vv;z[i+1]+=vv
 return z
def numerator(c,d):
 z=[c[0]]
 for i,di in enumerate(d,1):z=mul(z,di);z[-1]+=c[i]
 return z
def evaluate(v,x):
 z=0
 for vv in reversed(v):z=z*x+vv
 return z
nchecks=0
for n in range(1,6):
 for c in product(range(-2,3),repeat=n+1):
  d=[rng.randrange(1,15) for _ in range(n)]
  v=numerator(c,d);assert var(v)<=var(c)
  nchecks+=1
counts['arbitrary_coefficient_variation']=nchecks
nc=ni=nm=0
for a in range(6):
 for b in range(-1,6):
  for ell in [Q(1,7),Q(1,2),Q(1),Q(3),Q(7)]:
   for d0 in [Q(1,2),Q(1),Q(9)]:
    n=16;d=[Q(i)**a+Q(i)**b for i in range(1,n+1)]
    w=[Q(i)**(b+1) for i in range(1,n+1)]
    c=[-ell*d0]+[wi-ell*di for wi,di in zip(w,d)]
    assert var(c)<=2
    v=numerator(c,d);assert var(v)<=var(c);nc+=1
    for x in [Q(1,3),Q(2),Q(7)]:
     p=Q(1);H=Q(0);S=Q(0);G=c[0];D=Q(1)
     for wi,di,ci in zip(w,d,c[1:]):
      p*=x/(x+di);D*=x+di;H+=wi*p;S+=di*p;G+=ci*p
     assert S==x*(1-p)
     assert G==H-ell*(x+d0)+ell*x*p
     assert evaluate(v,x)/D==G;ni+=3
    if b>=a-1:
     rs=[Q(i)/(1+Q(i)**(a-b)) for i in range(1,101)]
     assert all(rs[i]<rs[i+1] for i in range(99));nm+=99
counts.update(source_sign_rows=nc,telescoping_and_tail_and_numerator_identities=ni,monotone_source_weight_differences=nm)
# Independent direct basis expansion, separate from Horner recurrence.
for trial in range(300):
 n=rng.randrange(1,16);ds=[Q(rng.randrange(1,20),rng.randrange(1,10)) for _ in range(n)]
 cs=[Q(rng.randrange(-20,21)) for _ in range(n+1)];direct=[Q(0)]*(n+1)
 for i,ci in enumerate(cs):
  term=[Q(1)]
  for dj in ds[i:]:term=mul(term,dj)
  for j,tj in enumerate(term):direct[i+j]+=ci*tj
 assert direct==numerator(cs,ds)
counts['independent_basis_expansions']=300
(P/'checks.json').write_text(json.dumps({'status':'PASS','counts':counts,'scope':'Finite exact checks of algebra and proof mechanisms; universal statements rely on the written proof, not these samples.'},indent=2)+'\n')
print(json.dumps(counts))
