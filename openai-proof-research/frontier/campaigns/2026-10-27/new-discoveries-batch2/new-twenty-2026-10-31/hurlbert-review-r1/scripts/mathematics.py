from itertools import permutations
from collections import deque
from pathlib import Path
import random,json
D=Path(__file__).resolve().parents[1]
tour=[tuple(map(int,s)) for s in '1234 2341 2413 4231 3421 3214 2134 1243 1423 4123 1342 3412 4132 1324 3142 1432 4321 4213 3241 2314 2143 2431 4312 3124'.split()]
def red(p):return tuple(sorted(p).index(x) for x in p)
def edges(t):
 L=len(t);g=[set() for _ in t]
 for i,p in enumerate(t):
  for a in range(len(p)):
   for b in range(len(p)):
    if p[a]<p[b]:g[(i+a)%L].add((i+b)%L)
 return g
def cyclic(t):
 g=edges(t);deg=[0]*len(g)
 for es in g:
  for v in es:deg[v]+=1
 q=deque(i for i,d in enumerate(deg) if d==0);count=0
 while q:
  u=q.popleft();count+=1
  for v in g[u]:
   deg[v]-=1
   if deg[v]==0:q.append(v)
 return count<len(g)
def valid(t):return len(set(t))==len(t) and set(t)==set(permutations(range(1,len(t[0])+1))) and all(red(p[1:])==red(t[(i+1)%len(t)][:-1]) for i,p in enumerate(t))
assert valid(tour) and cyclic(tour)
cycle=[2,5,8,10,13,15,18,20,23,2]
assert all(v in edges(tour)[u] for u,v in zip(cycle,cycle[1:]))
result={'witness_valid':True,'strict_cycle':cycle,'cycle_edges':[{'u':u,'v':v,'windows':[i for i,p in enumerate(tour) if any((i+a)%24==u and (i+b)%24==v and p[a]<p[b] for a in range(4) for b in range(4))]} for u,v in zip(cycle,cycle[1:])]}
for n in [2,3]:
 ps=list(permutations(range(1,n+1)));out={red(p[:-1]):[] for p in ps}
 for p in ps:out[red(p[:-1])].append(p)
 counts=[0,0]
 def dfs(t,used):
  if len(t)==len(ps):
   if red(t[-1][1:])==red(t[0][:-1]):counts[0]+=1;counts[1]+=cyclic(t)
   return
  for p in out[red(t[-1][1:])]:
   if p not in used:dfs(t+[p],used|{p})
 dfs([ps[0]],{ps[0]});result[str(n)]={'exhaustive_fixed_first_edge':counts[0],'nonrealizable':counts[1]}
n=4;ps=list(permutations(range(1,n+1)));out={red(p[:-1]):[] for p in ps}
for p in ps:out[red(p[:-1])].append(p)
r=random.Random(20261105);bad=0;examples=[]
for trial in range(50000):
 adj={v:r.sample(es,len(es)) for v,es in out.items()};stack=[(red(ps[0][:-1]),None)];back=[]
 while stack:
  v,e=stack[-1]
  if adj[v]:
   p=adj[v].pop();stack.append((red(p[1:]),p))
  else:
   _,p=stack.pop()
   if p is not None:back.append(p)
 t=back[::-1]
 assert valid(t)
 if cyclic(t):
  bad+=1
  if len(examples)<3:examples.append([''.join(map(str,p)) for p in t])
result['4']={'trials':50000,'nonrealizable':bad,'method':'seeded shuffled-adjacency Hierholzer, NOT uniform independent Euler-tour sampling','seed':20261105,'examples':examples}
(D/'mathematics.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result,indent=2))
