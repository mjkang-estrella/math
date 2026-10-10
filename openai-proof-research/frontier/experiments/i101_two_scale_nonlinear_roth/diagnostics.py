"""Finite exact diagnostics only. Pure computation, no writes or network."""
from fractions import Fraction as F
from functools import lru_cache
from itertools import product
from math import ceil
import json

def triples(n,q,d,m,first=2):
 return [(x,x+d*t,x+q*d*d*t*t,t) for t in range(first,m+1) for x in range(n) if x+q*d*d*t*t<n]
def edges(n,q,d,m):return [(x,z) for x,y,z,t in triples(n,q,d,m,1)]
@lru_cache(None)
def alpha(n,es):
 adj=[0]*n
 for x,z in es:adj[x]|=1<<z;adj[z]|=1<<x
 @lru_cache(None)
 def go(mask):
  if not mask:return 0
  v=(mask&-mask).bit_length()-1;r=mask^(1<<v)
  return max(go(r),1+go(r&~adj[v]))
 return go((1<<n)-1)
def variation(f,d):
 n=len(f)
 return sum(abs((f[x+d] if 0<=x+d<n else 0)-(f[x] if 0<=x<n else 0)) for x in range(-d,n))/2

def blocks(n,d,h):
 out=[]
 for r in range(d):
  chain=list(range(r,n,d));assert len(chain)>=h
  while len(chain)>=2*h:out.append(chain[:h]);chain=chain[h:]
  out.append(chain)
 return out

def avg(f,bs):
 g=[F(0)]*len(f)
 for b in bs:
  a=sum(f[i] for i in b)/F(len(b))
  for i in b:g[i]=a
 return g

def count(a,b,c,ts):return sum(a[x]*b[y]*c[z] for x,y,z,t in ts)
def cut_witness(r,ts):
 n=len(r);best=F(-1);bu=bv=None
 for u in product((-1,1),repeat=n):
  columns=[F(0)]*n
  for x,y,z,t in ts:columns[z]+=u[x]*r[y]
  value=sum(abs(v) for v in columns)
  if value>best:best=value;bu=u;bv=tuple(1 if v>=0 else -1 for v in columns)
 return best,bu,bv

def run():
 counts={k:0 for k in ['local_graph_independence','short_cutoff_indicator','weighted_graph','weighted_profile','block_average_count','three_slot_matchings','colored_walk_moments','bernoulli_expectations','run_selection','random_run_expectations','energy_refinements','periodic_strides']}
 # Independence bounds with exact finite square-free independence numbers.
 for n in range(1,11):
  for q,d,m in product(range(1,3),range(1,3),range(1,4)):
   es=edges(n,q,d,m);aa=alpha(n,tuple(es));Q=q*d*d;W=Q*m*m+1
   sa=alpha(m*m+1,tuple(edges(m*m+1,1,1,m)))
   B=min(n,ceil(n/W)*Q*sa)
   assert aa<=B;counts['local_graph_independence']+=1
   ts=triples(n,q,d,m)
   for mask in range(1<<n):
    f=[F((mask>>i)&1) for i in range(n)];a=sum(f);v=variation(f,d)
    assert 2*count(f,f,f,ts)>=a*a/B-3*a-v*m*(m+1)
    counts['short_cutoff_indicator']+=1
 # Weighted inequality and weighted middle stability; all ternary profiles.
 for n in range(1,7):
  es=edges(n,1,1,3);B=alpha(n,tuple(es));ts=triples(n,1,1,3)
  for vals in product(range(3),repeat=n):
   g=[F(v,2) for v in vals];s=sum(g)
   assert sum(v*v for v in g)+2*sum(g[x]*g[z] for x,z in es)>=s*s/B
   counts['weighted_graph']+=1
   ss=sum(v*v for v in g)
   assert 2*count(g,g,g,ts)>=ss*ss/B-sum(v**4 for v in g)-2*s-variation(g,1)*12
   counts['weighted_profile']+=1
 # Actual residual cut norm and block-preserving count.
 for n in range(4,9):
  for d in range(1,3):
   h=2
   if n<d*h:continue
   bs=blocks(n,d,h);es=edges(n,1,d,3);B=alpha(n,tuple(es));ts=triples(n,1,d,3)
   for mask in range(1<<n):
    f=[F((mask>>i)&1) for i in range(n)];a=sum(f);g=avg(f,bs);hh=[f[i]*g[i] for i in range(n)];s=sum(hh)
    assert sum(g)==a and s==sum(v*v for v in g) and s>=a*a/n
    assert variation(g,d)<=a/h
    diff=abs(count(f,f,f,ts)-count(f,g,f,ts))
    # Actual discrepancy is enough for a stronger diagnostic than a cut upper bound.
    assert 2*count(f,f,f,ts)>=s*s/B-sum(v*v for v in hh)-2*a-variation(g,d)*12-2*diff
    counts['block_average_count']+=1
 # All three fixed-vertex decompositions are matchings; max union degree.
 for n,q,d,m in product(range(2,31),range(1,4),range(1,4),range(2,6)):
  ts=triples(n,q,d,m)
  for slot in range(3):
   others=[i for i in range(3) if i!=slot];rows={};cols={};colors={}
   for xyz in ts:
    a,b,y=xyz[others[0]],xyz[others[1]],xyz[slot]
    colors.setdefault(y,[]).append((a,b));rows[a]=rows.get(a,0)+1;cols[b]=cols.get(b,0)+1
   for es in colors.values():assert len({x for x,z in es})==len(es)==len({z for x,z in es})
   assert max([0]+list(rows.values())+list(cols.values()))<=m-1
   counts['three_slot_matchings']+=1
 # Expected trace of Rademacher dilation powers = even-colored closed walks.
 for n,q,d,m in [(8,1,1,3),(12,1,1,3),(18,1,1,4),(18,1,2,3),(20,2,1,3)]:
  ts=triples(n,q,d,m)
  for slot in range(3):
   ot=[i for i in range(3) if i!=slot];adj=[[] for _ in range(2*n)]
   for xyz in ts:
    x,z,y=xyz[ot[0]],n+xyz[ot[1]],xyz[slot];adj[x].append((z,y));adj[z].append((x,y))
   for k in range(1,4):
    total=0
    for start in range(2*n):
     stack=[(start,0,0)]
     while stack:
      x,dep,par=stack.pop()
      if dep==2*k:
       total+=int(x==start and par==0);continue
      for z,y in adj[x]:stack.append((z,dep+1,par^(1<<y)))
    assert total<=2*n*(2*k)**(2*k)*(m-1)**k
    counts['colored_walk_moments']+=1
 # Exact inhomogeneous Bernoulli expectation, distinctness, vertex influences.
 for n in range(5,10):
  ts=triples(n,1,1,3);mu=[F(i+1,n+1) for i in range(n)];expect=F(0)
  for mask in range(1<<n):
   f=[(mask>>i)&1 for i in range(n)];p=F(1)
   for i in range(n):p*=mu[i] if f[i] else 1-mu[i]
   expect+=p*count(f,f,f,ts)
  assert expect==count(mu,mu,mu,ts)
  for x,y,z,t in ts:assert len({x,y,z})==3
  for i in range(n):assert sum(i in (x,y,z) for x,y,z,t in ts)<=6
  counts['bernoulli_expectations']+=1
 # Every nested B subset A, for all ternary encodings through n=7.
 for n in range(1,8):
  for d,L in product(range(1,4),range(2,5)):
   meanU=0
   for enc in product(range(3),repeat=n):
    A={i for i,e in enumerate(enc) if e};B={i for i,e in enumerate(enc) if e==2};U=set()
    for x in range(n):
     rr={x+j*d for j in range(L)}
     if rr<=A:U|=rr
    v=sum(x-d not in B for x in B)
    assert len(B)<=(L-1)*v+len(U);counts['run_selection']+=1
   for mask in range(1<<n):
    A={i for i in range(n) if (mask>>i)&1};U=set()
    for x in range(n):
     rr={x+j*d for j in range(L)}
     if rr<=A:U|=rr
    meanU+=len(U)
   assert F(meanU,1<<n)<=F(n*L,2**L);counts['random_run_expectations']+=1
 # Energy witness derived from exact signed cut optimization.
 for n in range(5,8):
  ts=triples(n,1,1,3)
  for mask in range(1<<n):
   f=[F((mask>>i)&1) for i in range(n)];g=avg(f,[list(range(n))]);r=[f[i]-g[i] for i in range(n)]
   value,u,v=cut_witness(r,ts)
   if not value:continue
   eps=value/(2*n*3);psi=[F(0)]*n
   for x,y,z,t in ts:psi[y]+=F(u[x]*v[z],3)
   quant={}
   for i,w in enumerate(psi):quant.setdefault((w+1)//(eps/4),[]).append(i)
   gp=avg(f,list(quant.values()));energy=sum((gp[i]-g[i])**2 for i in range(n))/n
   assert energy>=9*eps*eps/16
   assert len(quant)<=ceil(8/eps)+1
   counts['energy_refinements']+=1
 for d in range(1,26):
  A={i for i in range(1,101) if i%5 in (0,1)}
  if d%5:
   assert not any({x,x+d,x+2*d}<=A for x in A)
  else:assert sum(x-d not in A for x in A)<=d
  counts['periodic_strides']+=1
 f=[F(1)]*4+[F(0)];g=[F(4,5)]*5;ts=triples(5,1,1,2)
 assert count(f,f,f,ts)==0 and count(g,g,g,ts)==F(64,125)
 # The failed budget combination: c=1/8, fixed delta,K,k; error/main increases with M.
 failures={'smoothing_creates_triple':{'N':5,'A':[1,2,3,4],'actual':0,'averaged':'64/125'},'spectral_scalar_budget':'For c<=1/4, (log N)*M^(1/2-2c)/delta^4 is nondecreasing in M; increasing cutoff alone cannot make these bounds close.','periodic_low_variation':'For D not divisible by 5, every subset has V_D>=|B|/2.'}
 return {'status':'PASS','counts':counts,'retained_failed_proposals':failures,'scope':'finite exact diagnostics, not analytic proof or contribution certification'}
if __name__=='__main__':print(json.dumps(run(),indent=2,sort_keys=True))
