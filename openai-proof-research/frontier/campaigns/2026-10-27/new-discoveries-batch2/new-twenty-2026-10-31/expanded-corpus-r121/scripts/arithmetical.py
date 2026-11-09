import itertools,math,json
for n,R in [(3,20),(4,20)]:
 pairs=list(itertools.combinations(range(n),2));graphs=[]
 for mask in range(1<<len(pairs)):
  adj=[[] for _ in range(n)]
  for i,(a,b) in enumerate(pairs):
   if mask>>i&1:adj[a].append(b);adj[b].append(a)
  seen={0}
  for _ in range(n):seen|={b for a in seen for b in adj[a]}
  if len(seen)==n:graphs.append((mask,adj))
 rs=[r for r in itertools.product(range(1,R+1),repeat=n) if math.gcd(*r)==1]
 for mask,adj in graphs:
  count=0
  for r in rs:
   if all(sum(r[b] for b in adj[a])%r[a]==0 for a in range(n)):count+=1
  print(json.dumps(dict(n=n,edge_mask=mask,r_entries_max=R,bounded_primitive_structures=count,exact_total_asserted=False)),flush=True)
