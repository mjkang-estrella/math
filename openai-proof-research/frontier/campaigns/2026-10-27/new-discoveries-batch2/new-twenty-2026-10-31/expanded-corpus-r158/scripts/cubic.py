import sys,pathlib,json
N=int(sys.argv[1]);st=bool(int(sys.argv[2]));count=0;best=0;be=[]
edges=[(i,i+1) for i in range(N-1)]
if st:edges.append((0,N-1))
d=[1]*N
if not st:d[0]=d[-1]=2
def connected(a,r):
 seen={next(x for x in range(N) if x!=r)};todo=list(seen)
 for u in todo:
  for v in a[u]:
   if v!=r and v not in seen:seen.add(v);todo.append(v)
 return len(seen)==N-1
def rec():
 global count,best,be
 try:u=next(i for i in range(N) if d[i])
 except StopIteration:
  count+=1;p=[0]*N;p[0]=1;a=[[] for _ in range(N)]
  for x,y in edges:a[x].append(y);a[y].append(x)
  for v in range(1,N):p[v]=sum(p[x] for x in a[v] if x<v)
  if p[-1]>best and (st or all(connected(a,r) for r in range(N))):best=p[-1];be=edges[:]
  return
 from itertools import combinations
 for vs in combinations([v for v in range(u+2,N) if d[v] and not (st and u==0 and v==N-1)],d[u]):
  q=d[u];d[u]=0
  for v in vs:d[v]-=1;edges.append((u,v))
  rec()
  for v in reversed(vs):d[v]+=1;edges.pop()
  d[u]=q
rec()
print(json.dumps(dict(N=N,fixed_st=st,completions=count,maximum_biconnected_paths=best,best_edges=be,bound_squared=3**(N//2),violation=(best-1)**2>3**(N//2))),flush=True)
