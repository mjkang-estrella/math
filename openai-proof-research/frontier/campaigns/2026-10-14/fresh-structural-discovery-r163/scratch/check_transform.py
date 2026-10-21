# Exact finite enumeration independent of the generating-function derivation.
from fractions import Fraction as F
from itertools import product,combinations
from math import comb
from functools import lru_cache
import json
from pathlib import Path
R=Path('frontier/campaigns/2026-10-14/fresh-structural-discovery-r163')
p,s,e=F(2,3),F(1,5),F(1,6);q=1-p;a=1-2*e
r=(p+q*s)/(1+s);c=(p+q*s)/(p*a)
@lru_cache(None)
def C(g,d):
 return sum((F(comb(d,j)*comb(d+g-j,g-j))*s**(d-j)*(-s)**(g-j) for j in range(min(d,g)+1)),F(0))
@lru_cache(None)
def E(g,d):
 if d==0:return F(g==0)
 return sum((F(comb(d,j)*comb(d+g-j-1,g-j))*s**(d-j)*(-s)**(g-j) for j in range(min(d,g)+1)),F(0))
def block(x,N):
 out={}
 for l in range(N+1):
  for y in product((-1,1),repeat=l):
   z=q*(1-s)*s**l/F(2)**l
   if l:z+=p*(1-s)*s**(l-1)/F(2)**(l-1)*((1-e) if y[-1]==x else e)
   out[y]=z
 return out
def distribution(x,N):
 out={():F(1)}
 for bit in x:
  bs=block(bit,N);new={}
  for v,pv in out.items():
   for w,pw in bs.items():
    if len(v)+len(w)<=N:new[v+w]=new.get(v+w,F(0))+pv*pw
  out=new
 return out
@lru_cache(None)
def est(y,I,n):
 k=len(I);m=max(I);l=len(y)
 z=F(sum(comb(n,t)*r**t*(1-r)**(n-t) for t in range(m,n+1)))
 for j in range(1,k+1):
  for J in combinations(I,j):
   pre=(J[0]-1,)+tuple(J[h+1]-J[h]-1 for h in range(j-1))
   for ranks in combinations(range(1,l+1),j):
    ds=(ranks[0]-1,)+tuple(ranks[h+1]-ranks[h]-1 for h in range(j-1))
    term=c**j
    for g,d,rank in zip(pre,ds,ranks):term*=C(g,d)*y[rank-1]
    term*=sum((E(t-J[-1],l-ranks[-1]) for t in range(m,n+1)),F(0))
    z+=term
 return z/F(2)**k
def expected(x,I):
 ans=F(0);n=len(x)
 for mask in product((0,1),repeat=n):
  y=tuple((v+1)//2 for v,b in zip(x,mask) if b);m=sum(mask)
  if len(y)>=max(I) and all(y[i-1] for i in I):ans+=r**m*(1-r)**(n-m)
 return ans
rows=[]
for x in product((-1,1),repeat=2):
 for N in (4,8):
  dist=distribution(x,N)
  for I in ((1,),(2,),(1,2)):
   v=sum((prob*est(y,I,len(x)) for y,prob in dist.items()),F(0));target=expected(x,I)
   rows.append({'x':list(x),'N':N,'I':list(I),'estimate':str(v),'target':str(target),'absolute_error':float(abs(v-target)),'discarded_mass':float(1-sum(dist.values()))})
for x in product((-1,1),repeat=2):
 for I in ((1,),(2,),(1,2)):
  v=[z for z in rows if z['x']==list(x) and z['I']==list(I)]
  assert v[1]['absolute_error']<F(1,1000)
  assert v[1]['absolute_error']<v[0]['absolute_error']
# Demonstrate the missing-length bug independently under ordinary deletion:
# x=(+1,+1), I={2}; naive (1+E padded sign at rank2)/2 != E bit rank2.
naive=(1+r*r)/2;correct=r*r
assert naive!=correct
out={'scope':'finite n=2 diagnostic only; no universal mathematical/contribution gate','parameters':{'p':str(p),'s':str(s),'e':str(e),'r':str(r)},'rows':rows,'missing_length_example':{'naive':str(naive),'correct':str(correct)},'max_error_N8':max(z['absolute_error'] for z in rows if z['N']==8)}
(R/'evidence/transform-diagnostic.json').write_text(json.dumps(out,indent=2)+'\n')
print('24 exact finite comparisons; max N=8 truncation error',out['max_error_N8']);print('Missing-length bug:',naive,'versus',correct)
