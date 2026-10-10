"""Exact, deterministic finite tests. No filesystem writes; JSON goes to stdout."""
from fractions import Fraction as Q
from itertools import combinations, permutations
from math import comb
import json
counts={};examples={}
def ck(ok,kind):
 assert ok,kind
 counts[kind]=counts.get(kind,0)+1
def masks(N,k):return [sum(1<<i for i in c) for c in combinations(range(N),k)]
def mean(xs):return sum(xs,Q())/len(xs)
def var(xs):
 a=mean(xs);return mean([(x-a)**2 for x in xs])
def examine(N,m,vals):
 sl=masks(N,m);f=dict(zip(sl,map(Q,vals)));mu=mean(list(f.values()));v=var(list(f.values()))
 pairs=[(a,b) for a in range(N) for b in range(a+1,N)]
 total=sum((f[x]-f[x^(1<<a)^(1<<b)])**2 for x in sl for a,b in pairs if ((x>>a)&1)!=((x>>b)&1))
 delta=Q(total,len(sl)*m*(N-m));I=Q(m*(N-m),N)*delta
 ck(v<=I/2,'slice_poincare')
 g={}
 for k in range(N+1):
  for x in masks(N,k):
   compatible=[f[y] for y in sl if (y&x==x if k<=m else y&x==y)]
   g[x]=mean(compatible)
  gv=[g[x] for x in masks(N,k)]
  ck(mean(gv)==mu,'layer_mean')
  loss=v-var(gv)
  if k<m:bound=Q((m-k)*(N-m),2*(N-k))*delta
  elif k>m:bound=Q((k-m)*m,2*k)*delta
  else:bound=Q()
  ck(0<=loss<=bound,'conditional_variance_bound')
 for k in range(N):
  av=mean([abs(g[x|1<<e]-g[x]) for x in masks(N,k) for e in range(N) if not(x>>e&1)])
  factor=Q(N-m,N-k) if k<m else Q(m,k+1)
  ck(av<=factor*delta,'adjacent_layer_L1_bound')
 p=Q(m,N);weights={x:p**x.bit_count()*(1-p)**(N-x.bit_count()) for x in g}
 vg=sum(weights[x]*(g[x]-mu)**2 for x in g)
 deviation=sum(Q(comb(N,k))*p**k*(1-p)**(N-k)*abs(k-m) for k in range(N+1))
 ck(v-vg<=delta*deviation/2,'binomial_variance_loss')
 l1=sum(p**x.bit_count()*(1-p)**(N-1-x.bit_count())*abs(g[x|1<<e]-g[x]) for e in range(N) for x in g if not(x>>e&1))
 ck(l1<=N*delta,'product_L1_gradient')
 # Coarea computed independently by exact threshold intervals.
 levels=sorted(set([Q(),Q(1)]+list(g.values())))
 cv=Q();ci=Q()
 for a,b in zip(levels,levels[1:]):
  t=(a+b)/2;h={x:Q(g[x]>t) for x in g};hm=sum(weights[x]*h[x] for x in g)
  cv+=(b-a)*hm*(1-hm)
  ci+=(b-a)*sum(p**x.bit_count()*(1-p)**(N-1-x.bit_count())*abs(h[x|1<<e]-h[x]) for e in range(N) for x in g if not(x>>e&1))
 ck(vg<=cv,'coarea_variance');ck(ci==l1,'coarea_gradient')
 # Priority fiber disagreements: all rankings of other coordinates for small N.
 if N<=4:
  Ds=[]
  for e in range(N):
   bad=0;orders=list(permutations([i for i in range(N) if i!=e]))
   for order in orders:
    a=sum(1<<i for i in order[:m]);b=(a^(1<<order[m-1]))|(1<<e)
    bad+=f[a]!=f[b]
   Ds.append(Q(bad,len(orders)))
  ck(sum(Ds)==N*delta,'priority_fiber_identity')
for N in range(2,6):
 for m in range(1,N):
  sz=comb(N,m)
  for code in range(1<<sz):examine(N,m,[(code>>j)&1 for j in range(sz)])
# Graph-invariant functions, enumerate isomorphism orbits on every K4 slice.
n=4;edges=list(combinations(range(n),2));N=len(edges);index={e:i for i,e in enumerate(edges)}
for m in range(1,N):
 sl=masks(N,m);orbits=[];left=set(sl)
 while left:
  x=min(left);orb=set()
  for pi in permutations(range(n)):
   y=sum(1<<index[tuple(sorted((pi[a],pi[b])))] for i,(a,b) in enumerate(edges) if x>>i&1);orb.add(y)
  orbits.append(orb);left-=orb
 for code in range(1<<len(orbits)):
  f={x:(code>>i)&1 for i,orb in enumerate(orbits) for x in orb}
  examine(N,m,[f[x] for x in sl])
# Wedge obstruction: exact enumeration independent of formula.
for n in range(4,13):
 E=list(combinations(range(n),2));N=len(E);sl=list(combinations(range(N),2));a=Q(sum(bool(set(E[i])&set(E[j])) for i,j in sl),len(sl))
 delta=Q()
 for i,j in sl:
  old=bool(set(E[i])&set(E[j]))
  for kept in [i,j]:
   for b in range(N):
    if b in (i,j):continue
    delta+=old!=bool(set(E[kept])&set(E[b]))
 delta/=len(sl)*2*(N-2)
 I=Q(2*(N-2),N)*delta
 ck(a==Q(4,n+1),'wedge_probability')
 ck(a*(1-a)/I==Q(n*(n-1),4*(n+1)*(n-2)),'wedge_ratio')
 examples[str(n)]={'variance':str(a*(1-a)),'swap_influence':str(I),'ratio':str(a*(1-a)/I)}
# Binary threshold fiber influence and tail bound, without random priorities.
for q in range(1,9):
 M=1<<q
 for t in range(M+1):
  influences=[Q(sum((x<t)!=((x^(1<<(q-j)))<t) for x in range(M)),M) for j in range(1,q+1)]
  for j,inf in enumerate(influences,1):ck(inf<=Q(1,1<<(j-1)),'bit_fiber_bound')
  for b in range(q+1):ck(sum(influences[b:])<=Q(2,1<<b),'bit_tail_bound')
# Colored repeated-edge support contradicts naive uncolored capture.
for k in range(3,10):
 b=k+1;ck(b<=Q(k*k,2),'colored_support_cutoff');ck(b>k,'colored_capture_fails')
# All N=3 families, three biases: two-row signed Fourier cover calculation.
for N in range(1,4):
 for p in [Q(1,4),Q(1,3),Q(1,2)]:
  X=range(1<<N);mass={x:p**x.bit_count()*(1-p)**(N-x.bit_count()) for x in X}
  for fam in range(1,1<<(1<<N)):
   D=[x for x in X if fam>>x&1];mu=sum(mass[x] for x in D);w={}
   for U in X:
    c=Q()
    for x in D:
     outside=x&~U;inside=x&U
     c+=(-1)**inside.bit_count()*p**outside.bit_count()*(1-p)**(N-U.bit_count()-outside.bit_count())
    w[U]=((1-p)**U.bit_count()*c)**2
   bad=[x for x in X if all(x&(a|b)!=x for a in D for b in D)]
   for x in bad:
    ck(sum((-1)**U.bit_count()*w[U] for U in X if U&x==U)==0,'signed_two_row_identity')
    ck(sum(w[U] for U in X if U and U&x==U)>=mu**2,'fractional_cover')
   cost=sum(p**U.bit_count()*w[U] for U in X if U)/mu**2
   ck(cost<=(1-p)*(1-mu)/mu,'fractional_cost')
# Matchings: exact spread containment products and isolation moments.
for n in range(2,42,2):
 prod=1
 for s in range(1,n//2+1):
  prod*=n-2*s+1
  # Weaker rational spread constant 6/n avoids numeric e.
  ck(Q(1,prod)<=Q(6,n)**s,'matching_spread_6')
for n in range(4,30):
 for p in [Q(1,n),Q(2,n),Q(1,2)]:
  ez=n*(1-p)**(n-1);ez2=ez+n*(n-1)*(1-p)**(2*n-3)
  ck((ez2-ez**2)/ez**2<=1/ez+p/(1-p),'isolation_second_moment')
print(json.dumps({'assertions':sum(counts.values()),'counts':counts,'wedge_examples':examples},sort_keys=True,indent=2))
