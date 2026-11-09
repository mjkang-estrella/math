import itertools,json,time
# Search total orders, modulo vertex transitivity (first vertex 0).
for n in range(6,23,2):
 for a,b in itertools.combinations(range(1,n//2),2):
  adj=[sum(1<<j for j in range(n) if (j-i)%n in {a,b,n-a,n-b,n//2}) for i in range(n)];nodes=0;budget=100000
  def good(order):
   k=len(order);reach={x:0 for x in order}
   for i in range(k-1,-1,-1):
    x=order[i]
    for y in order[i+1:]:
     if adj[x]>>y&1:reach[x]|=(1<<y)|reach[y]
   v=order[-1]
   for u in order[:-1]:
    if not(adj[u]>>v&1):continue
    interval=[x for x in order if (x==u or reach[u]>>x&1) and (x==v or reach[x]>>v&1)]
    for x in interval:
     if any(reach[x]>>y&1 and not(adj[x]>>y&1) for y in interval):return False
   return True
  def search(order,unused):
   global nodes
   nodes+=1
   if nodes>budget:return None
   if not unused:return order
   for v in unused:
    oo=order+[v]
    if good(oo):
     z=search(oo,unused-{v})
     if z is not None:return z
   return None
  t=time.monotonic();ans=search([0],set(range(1,n)))
  print(json.dumps({'n':n,'jumps':[a,b,n//2],'nodes':nodes,'status':'semitransitive_order_found' if ans else ('inconclusive_node_cap' if nodes>budget else 'exhaustive_no_order'),'order':ans,'seconds':time.monotonic()-t}),flush=True)
