import itertools,json
for n in range(3,7):
 edges=list(itertools.combinations(range(n),2));tested=0;bad=[]
 for mask in range(1<<len(edges)):
  m=mask.bit_count();c=m-n+1
  if c<2:continue
  adj=[set() for _ in range(n)]
  for i,(x,y) in enumerate(edges):
   if mask>>i&1:adj[x].add(y);adj[y].add(x)
  seen={0};stack=[0]
  while stack:
   x=stack.pop()
   for y in adj[x]-seen:seen.add(y);stack.append(y)
  if len(seen)!=n:continue
  tested+=1;L=0
  for v in range(n):
   if len(adj[v])<3:continue
   legs=0
   for w in adj[v]:
    last=v;x=w
    while len(adj[x])==2:last,x=x,next(iter(adj[x]-{last}))
    legs+=len(adj[x])==1
   L+=max(0,legs-1)
  bound=L+2*c
  if bound>=n-1:continue
  dist=[]
  for v in range(n):
   row=[n]*n;row[v]=0;q=[v]
   for x in q:
    for y in adj[x]:
     if row[y]==n:row[y]=row[x]+1;q.append(y)
   dist.append(row)
  good=False
  for S in itertools.combinations(range(n),bound):
   if len({tuple(dist[s][v] for s in S) for v in range(n)})==n:good=True;break
  if not good:bad.append(mask)
 print(json.dumps({'n':n,'labelled_graph_masks':1<<len(edges),'connected_c_at_least_2_tested':tested,'failures':bad}),flush=True)
