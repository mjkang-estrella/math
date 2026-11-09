from pathlib import Path
from itertools import permutations
from collections import deque
import random,json,math
D=Path(__file__).resolve().parents[1]
def red(p):return tuple(sorted(p).index(x) for x in p)
def graph(t):
 g=[set() for _ in t];L=len(t)
 for i,p in enumerate(t):
  for a in range(len(p)):
   for b in range(a+1,len(p)):
    u,v=((i+a)%L,(i+b)%L) if p[a]<p[b] else ((i+b)%L,(i+a)%L)
    g[u].add(v)
 return g
def bad(t):
 g=graph(t);ind=[0]*len(t)
 for row in g:
  for v in row:ind[v]+=1
 q=deque(i for i,d in enumerate(ind) if d==0);count=0
 while q:
  u=q.popleft();count+=1
  for v in g[u]:
   ind[v]-=1
   if ind[v]==0:q.append(v)
 return count<len(t)
def valid(t):return len(t)==math.factorial(len(t[0])) and set(t)==set(permutations(range(1,len(t[0])+1))) and all(red(p[1:])==red(t[(i+1)%len(t)][:-1]) for i,p in enumerate(t))
def setup(n):
 ps=list(permutations(range(1,n+1)));out={red(p[:-1]):[] for p in ps}
 for p in ps:out[red(p[:-1])].append(p)
 return ps,out
def tour(adj,start):
 stack=[(start,None)];back=[]
 while stack:
  v,p=stack[-1]
  if adj[v]:
   e=adj[v].pop();stack.append((red(e[1:]),e))
  else:
   _,e=stack.pop()
   if e is not None:back.append(e)
 return back[::-1]
witness=[tuple(map(int,s)) for s in '1234 2341 2413 4231 3421 3214 2134 1243 1423 4123 1342 3412 4132 1324 3142 1432 4321 4213 3241 2314 2143 2431 4312 3124'.split()]
assert valid(witness) and bad(witness)
cycle=[2,5,8,10,13,15,18,20,23,2];table=[]
for u,v in zip(cycle,cycle[1:]):
 a=0;b=(v-u)%len(witness);assert b<4 and witness[u][a]<witness[u][b]
 table.append(dict(window=u,permutation=''.join(map(str,witness[u])),offsets=[a,b],positions=[u,v],ranks=[witness[u][a],witness[u][b]]))
r={'witness':[''.join(map(str,p)) for p in witness],'euler':valid(witness),'vertices':len(witness),'comparison_edges':sum(map(len,graph(witness))),'comparison_graph':[sorted(es) for es in graph(witness)],'cycle':cycle,'forcing_table':table}
r['exhaustive']={}
for n in [2,3]:
 ps,out=setup(n);counts=[0,0]
 def dfs(t,used):
  if len(t)==len(ps):
   if red(t[-1][1:])==red(t[0][:-1]):counts[0]+=1;counts[1]+=bad(t)
   return
  for p in out[red(t[-1][1:])]:
   if p not in used:dfs(t+[p],used|{p})
 dfs([ps[0]],{ps[0]});r['exhaustive'][str(n)]=counts
ps,out=setup(4);rng=random.Random(20261105);fail=0
for _ in range(50000):
 t=tour({v:rng.sample(es,len(es)) for v,es in out.items()},red(ps[0][:-1]));assert valid(t);fail+=bad(t)
assert fail==7;r['review_search']=dict(seed=20261105,trials=50000,failures=fail)
rng=random.Random(356270)
for trial in range(30000):
 t=tour({v:rng.sample(es,len(es)) for v,es in out.items()},red(ps[0][:-1]))
 if bad(t):break
assert trial+1==8465;r['discovery_search']=dict(seed=356270,trials=trial+1,failures=1)
base=[tuple(map(int,s)) for s in '1234 2341 3412 4231 3421 4321 4312 4123'.split()];assert bad(base)
assert all(red(p[1:])==red(base[(i+1)%len(base)][:-1]) for i,p in enumerate(base))
assert set(base)=={p for p in ps if all(red(q) not in [(0,2,1),(1,0,2)] for q in __import__('itertools').combinations(p,3))}
assert all(v in graph(base)[u] for u,v in [(4,1),(7,4),(1,7)])
rest=set(ps)-set(base);rng=random.Random(2009);tested=0;fail=0
for _ in range(20000):
 k=rng.randrange(8);adj={v:[] for v in out}
 for p in sorted(rest):adj[red(p[:-1])].append(p)
 for v in adj:rng.shuffle(adj[v])
 ext=tour(adj,red(base[k][:-1]))
 if len(ext)!=16:continue
 t=base[:k]+ext+base[k:];assert valid(t);tested+=1;fail+=bad(t)
assert tested==20000 and fail==0;r['albert_west']=dict(base=[''.join(map(str,p)) for p in base],tested=tested,failures=fail,seed=2009)
word=tuple(map(int,'123412534153214532413254'));windows=[tuple(word[(i+a)%len(word)] for a in range(4)) for i in range(len(word))];types=[tuple(x+1 for x in red(p)) for p in windows];assert valid(types) and not bad(types)
r['cdg']=dict(word=''.join(map(str,word)),length=len(word),distinct_symbols=len(set(word)),windows=[''.join(map(str,p)) for p in windows],types=[''.join(map(str,p)) for p in types],euler=True)
(D/'recomputed.json').write_text(json.dumps(r,indent=2)+'\n');print(json.dumps({k:v for k,v in r.items() if k in ['exhaustive','review_search','discovery_search','comparison_edges']},indent=2))
