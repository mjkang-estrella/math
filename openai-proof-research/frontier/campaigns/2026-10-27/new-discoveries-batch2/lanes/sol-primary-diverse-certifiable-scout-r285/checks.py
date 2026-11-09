from research import *
from functools import lru_cache
from itertools import permutations
def adj(n,edges):
 a=[0]*n
 for u,v in edges:a[u]|=1<<v;a[v]|=1<<u
 return a
def solve(a,kind='A'):
 n=len(a);full=(1<<n)-1
 @lru_cache(None)
 def f(s):
  if s==full:return ()
  for v in range(n):
   if s>>v&1:continue
   d=(a[v]&s).bit_count();remain=a[v]&~(s|1<<v)
   if d==0 or d%2 or (kind=='B' and not remain):
    q=f(s|1<<v)
    if q is not None:return (v,)+q
  return None
 return f(0)
def valid(a,p,kind):
 s=0
 for v in p:
  d=(a[v]&s).bit_count()
  if d>0 and d%2==0 and (kind=='A' or a[v]&~(s|1<<v)):return False
  s|=1<<v
 return True
def greedy_reverse(a):
 s=(1<<len(a))-1;order=[]
 while s:
  eligible=[v for v in range(len(a)) if s>>v&1 and ((a[v]&s).bit_count()==0 or (a[v]&s).bit_count()%2)]
  if not eligible:return None
  v=min(eligible);s^=1<<v;order.append(v)
 return tuple(reversed(order))
def dualcritical(a):
 n=len(a)
 @lru_cache(None)
 def f(s):
  if s==(1<<n)-1:return True
  return any(f(s|1<<v) for v in range(n) if not s>>v&1 and (s==0 or (a[v]&s).bit_count()%2))
 return f(0)
def source_set_reduction(a):
 n=len(a)
 for s in range(1,1<<n):
  if any(a[v]&s for v in range(n) if s>>v&1):continue
  rest=[v for v in range(n) if not s>>v&1];edges=[]
  for i,v in enumerate(rest):
   for j,w in enumerate(rest[:i]):
    if a[v]>>w&1:edges.append((i,j))
   if (a[v]&s).bit_count()%2:edges.append((i,len(rest)))
  if dualcritical(adj(len(rest)+1,edges)):return s
 return None
rows=[]
for n in range(1,6):
 pairs=[(i,j) for i in range(n) for j in range(i)]
 for bits in range(1<<len(pairs)):
  edges=[e for k,e in enumerate(pairs) if bits>>k&1];a=adj(n,edges)
  assert (solve(a) is not None)==(source_set_reduction(a) is not None)
  for kind in ['A','B']:
   q=solve(a,kind); brute=next((p for p in permutations(range(n)) if valid(a,p,kind)),None)
   assert (q is None)==(brute is None)
   if q is not None:
    assert valid(a,q,kind)
    if kind=='A':
     s=0;sources=0
     for v in q:
      sources+=not(a[v]&s);s|=1<<v
     assert (len(edges)-n+sources)%2==0
  if solve(a) is not None and greedy_reverse(a) is None and not rows:rows.append(dict(kind='greedy_failure',n=n,edges=edges,order=solve(a)))
# C4 with a leaf: parity prevents every unique-source odd-indegree acyclic orientation.
edges=[(0,1),(1,2),(2,3),(3,0),(0,4)];a=adj(5,edges);q=solve(a);assert q is not None
assert (len(edges)-5+1)%2==1
rows.append(dict(kind='type_A_not_dualcritical',n=5,edges=edges,order=q,parity='m=5,n=5 forces even number of sources'))
(L/'exact-checks.json').write_text(json.dumps(dict(exhaustive_graphs_through_n=5,graphs=1099,methods=['subset DP','independent permutation verifier','source parity identity','independent-source-set dual-critical reduction'],witnesses=rows),indent=2))
print(json.dumps(rows))
