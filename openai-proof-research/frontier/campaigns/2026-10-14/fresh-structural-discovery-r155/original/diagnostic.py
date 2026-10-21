"""Bounded exact finite diagnostics, not a proof or a novelty test. Stdlib only."""
from functools import lru_cache
from itertools import product, combinations
from collections import Counter,defaultdict
from fractions import Fraction
import json

def parts(n,cap=None):
 if n==0:yield ();return
 for a in range(min(n,cap or n),0,-1):
  for p in parts(n-a,a):yield (a,)+p

def words(r):
 if not sum(r):yield ();return
 for i,a in enumerate(r):
  if a:
   s=list(r);s[i]-=1
   for w in words(tuple(s)):yield (i,)+w

def hessenbergs(n):
 for h in product(*[range(i+1,n+1) for i in range(n)]):
  if all(h[i]<=h[i+1] for i in range(n-1)):yield h

def invmat(a):
 n=len(a);a=[[Fraction(x) for x in row]+[Fraction(i==j) for j in range(n)] for i,row in enumerate(a)]
 for j in range(n):
  k=next(k for k in range(j,n) if a[k][j]);a[j],a[k]=a[k],a[j];v=a[j][j];a[j]=[x/v for x in a[j]]
  for i in range(n):
   if i!=j:
    v=a[i][j];a[i]=[x-v*y for x,y in zip(a[i],a[j])]
 return [row[n:] for row in a]

def product_coefficient(shape,mu,elementary):
 states={(0,)*len(mu):1}
 for size in shape:
  if elementary:
   choices=[tuple(int(i in z) for i in range(len(mu))) for z in combinations(range(len(mu)),size)]
  else:choices=[z for z in product(*[range(x+1) for x in mu]) if sum(z)==size]
  new=Counter()
  for a,v in states.items():
   for b in choices:
    c=tuple(x+y for x,y in zip(a,b))
    if all(x<=y for x,y in zip(c,mu)):new[c]+=v
  states=new
 return states.get(mu,0)

@lru_cache(None)
def matrices(N):
 ps=list(parts(N));E=[[product_coefficient(l,mu,True) for l in ps] for mu in ps];H=[[product_coefficient(l,mu,False) for l in ps] for mu in ps]
 return ps,invmat(E),invmat(H)

def poly_mul(a,b):
 c=Counter()
 for i,x in a.items():
  for j,y in b.items():c[i+j]+=x*y
 return +c

def insertion_poly(h,r):
 ans=Counter({0:1})
 for a,num in enumerate(r):
  L=sum(r[b] for b in range(a) if a<h[b]);dp={(0,0):1}
  # Multisets of num slot digits from 0,...,L, hence Gaussian binomial.
  t={(0,0):1}
  for d in range(L+1):
   u=Counter()
   for (k,e),v in t.items():
    for m in range(num-k+1):u[k+m,e+m*d]+=v
   t=u
  ans=poly_mul(ans,Counter({e:v for (k,e),v in t.items() if k==num}))
 return ans

def run_case(h,r):
 n=len(h);N=sum(r);ps,Einv,Hinv=matrices(N);ws=list(words(r));wid={w:i for i,w in enumerate(ws)};par=list(range(len(ws)))
 def find(a):
  while par[a]!=a:par[a]=par[par[a]];a=par[a]
  return a
 def union(a,b):
  a,b=find(a),find(b)
  if a!=b:par[b]=a
 def comparable(a,c):return a<c and c>=h[a]
 def edge(a,b):return a!=b and max(a,b)<h[min(a,b)]
 def inv(w):return sum(a>b and edge(a,b) for i,a in enumerate(w) for b in w[i+1:])
 for w in ws:
  for i in range(N-1):
   a,c=w[i:i+2]
   if comparable(min(a,c),max(a,c)):
    v=w[:i]+(c,a)+w[i+2:];union(wid[w],wid[v])
  for i in range(N-2):
   z=w[i:i+3];a,b,c=sorted(z)
   if a<b<c and edge(a,b) and edge(b,c) and comparable(a,c):
    for x,y in [((b,a,c),(a,c,b)),((b,c,a),(c,a,b))]:
     if z==x or z==y:
      v=w[:i]+(y if z==x else x)+w[i+3:];union(wid[w],wid[v])
 groups=defaultdict(list)
 for w in ws:groups[find(wid[w])].append(w)
 aggregates=[Counter() for _ in ps];records=[]
 for C in groups.values():
  d=inv(C[0]);assert all(inv(w)==d for w in C)
  Ecounts=[]
  for shape in ps:
   c=0
   for w in C:
    p=0;ok=True
    for k in shape:
     z=w[p:p+k];p+=k
     if not all(comparable(z[j+1],z[j]) for j in range(k-1)):ok=False;break
    c+=ok
   Ecounts.append(c)
  # m_shape = sum_k (E^{-1})[k,shape] e_k.
  b=[sum(Einv[k][j]*Ecounts[k] for k in range(len(ps))) for j in range(len(ps))]
  mon=[]
  for mu in ps:
   boundary=set();t=0
   for a in mu[:-1]:t+=a;boundary.add(t-1)
   mon.append(sum(all(i in boundary for i in range(N-1) if comparable(w[i+1],w[i])) for w in C))
  bh=[sum(Hinv[j][k]*mon[k] for k in range(len(ps))) for j in range(len(ps))]
  assert b==bh,(h,r,'duality')
  assert all(x.denominator==1 for x in b)
  assert all(x>=0 for x in b),(h,r,'finite negative class',b)
  for j,x in enumerate(b):aggregates[j][d]+=int(x)
  records.append({'representative':[x+1 for x in min(C)],'size':len(C),'inv':d,'h_coefficients':{str(ps[j]):int(x) for j,x in enumerate(b) if x}})
 total=Counter()
 for a in aggregates:total.update(a)
 adm=Counter(inv(w) for w in ws if all(not comparable(w[i],w[i+1]) for i in range(N-1)))
 assert +total==adm==insertion_poly(h,r),(h,r,'insert')
 # Direct proper set-coloring coefficient of x_1^mu_1 ... x_k^mu_k.
 indeps={k:[z for z in combinations(range(n),k) if all(not edge(a,b) for a,b in combinations(z,2))] for k in range(n+1)}
 for row,mu in enumerate(ps):
  state={(0,)*n:Counter({0:1})}
  for k in mu:
   nxt=defaultdict(Counter)
   for a,pol in state.items():
    for S in indeps.get(k,[]):
     b=tuple(a[i]+(i in S) for i in range(n))
     if any(b[i]>r[i] for i in range(n)):continue
     shift=sum(a[i] for j in S for i in range(j) if edge(i,j))
     for d,v in pol.items():nxt[b][d+shift]+=v
   state=nxt
  direct=+state.get(r,Counter());reconstructed=Counter()
  for shape,pol in zip(ps,aggregates):
   v=product_coefficient(shape,mu,True)
   for d,c in pol.items():reconstructed[d]+=v*c
  assert direct==+reconstructed,(h,r,'color')
 return len(ws),len(groups),records

cases=[]
for n in range(1,4):
 for h in hessenbergs(n):
  for r in product(range(3),repeat=n):
   if 0<sum(r)<=5:cases.append((h,r))
for n in (4,5):
 for h in hessenbergs(n):cases.append((h,(1,)*n))
for h in hessenbergs(4):cases.append((h,(2,1,1,1)))
W=C=0;example=None
for h,r in cases:
 w,c,rec=run_case(h,r);W+=w;C+=c
 if h==(3,3,4,4) and r==(1,1,1,1):example=rec
print(json.dumps({'cases':len(cases),'words':W,'components':C,'max_total_demand':5,'checked':'independent class h-expansion / noncommutative monomial duality, direct set-coloring e-expansion, multiset insertion Gaussian product; nonnegativity only for tested finite classes','example_h':[3,3,4,4],'example_demand':[1,1,1,1],'example_components':example},indent=2))
