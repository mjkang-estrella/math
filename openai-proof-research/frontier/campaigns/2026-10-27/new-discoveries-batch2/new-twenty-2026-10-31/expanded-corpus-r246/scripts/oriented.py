import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];rows=[]
for n in range(2,6):
 es=list(itertools.combinations(range(n),2));count=0;prem=0;sinkfree=0
 for states in itertools.product(range(3),repeat=len(es)):
  adj=[0]*n
  for (u,v),x in zip(es,states):
   if x==1:adj[u]|=1<<v
   if x==2:adj[v]|=1<<u
  ls=[]
  for v in range(n):
   sec=0
   for u in range(n):
    if adj[v]>>u&1:sec|=adj[u]
   sec &= ~adj[v] & ~(1<<v)
   if sec.bit_count()>=adj[v].bit_count():ls.append(v)
  count+=1
  if all(adj):sinkfree+=1
  if len(ls)==1:
   prem+=1
   if adj[ls[0]]:print('COUNTEREXAMPLE',n,adj,flush=True);raise SystemExit
 row=dict(n=n,graphs=count,unique_large=prem,sinkfree=sinkfree);rows.append(row);print(row,flush=True)
(D/'oriented-coverage.json').write_text(json.dumps(rows,indent=2))
