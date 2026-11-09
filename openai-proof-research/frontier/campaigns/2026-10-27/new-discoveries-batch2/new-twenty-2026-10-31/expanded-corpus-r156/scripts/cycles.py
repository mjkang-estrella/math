import itertools,random,time,json
from pathlib import Path
random.seed(156);out=[];start=time.monotonic()
def check(n,E):
 adj=[set() for _ in range(n)]
 for a,b in E:adj[a].add(b);adj[b].add(a)
 cs=set()
 def dfs(s,path):
  if len(path)==5:
   if s in adj[path[-1]]:cs.add(tuple(sorted(tuple(sorted((path[i],path[(i+1)%5]))) for i in range(5))))
   return
  for v in adj[path[-1]]:
   if v>s and v not in path:dfs(s,path+[v])
 for s in range(n):dfs(s,[s])
 if not cs:return True,0
 C=[set(c) for c in cs]
 def solve(C):
  if not C:return True
  for e in min(C,key=len):
   off=set().union(*(c for c in C if e in c))-{e}
   remain=[c-off for c in C if e not in c]
   if all(remain) and solve(remain):return True
  return False
 return solve(C),len(C)
for n in [8,10,12,14,16,18,20,24,30,40,50,60]:
 attempted=0;tested=0;nonempty=0;maxc=0
 while tested<600 and attempted<30000:
  attempted+=1;stubs=list(range(n))*3;random.shuffle(stubs);E=set();good=True
  for a,b in zip(stubs[::2],stubs[1::2]):
   e=tuple(sorted((a,b)))
   if a==b or e in E:good=False;break
   E.add(e)
  if not good:continue
  adj=[set() for _ in range(n)]
  for a,b in E:adj[a].add(b);adj[b].add(a)
  if any(adj[a]&adj[b] for a,b in E):continue
  # Half of trials remove random edges to cover subcubic irregular cases.
  if tested%2:E={e for e in E if random.random()>.12}
  ok,c=check(n,E);tested+=1;nonempty+=bool(c);maxc=max(c,maxc)
  if not ok:
   Path('outputs/cycles-witness.json').write_text(json.dumps({'n':n,'edges':sorted(E)}));print('COUNTEREXAMPLE',n,sorted(E),flush=True);raise SystemExit
 out.append({'n':n,'configuration_pairings_attempted':attempted,'simple_trianglefree_graphs_tested':tested,'with_5cycles':nonempty,'max_5cycles':maxc});print(out[-1],flush=True)
Path('outputs/cycles-search.json').write_text(json.dumps({'rows':out,'seconds':time.monotonic()-start,'scope':'Seeded random configuration graphs, alternating cubic and edge-deleted. Not exhaustive.'},indent=2))
