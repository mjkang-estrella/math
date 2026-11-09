import math,resource,json
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
for k in range(1,25):
 gcd=[[math.gcd(d,v) for v in range(k+1)] for d in range(k+1)];count=0;nodes=0;noendpoint=[]
 def dfs(assigned,unused):
  global count,nodes
  nodes+=1
  if nodes>200000:raise RuntimeError('node cap')
  if not unused:
   count+=1
   if assigned[0]!=1 and assigned[k-1]!=1:noendpoint.append([assigned[i] for i in range(k)])
   return
  best=None;vals=None
  for i in range(k):
   if i in assigned:continue
   allowed=[v for v in unused if all(gcd[abs(i-j)][v]==gcd[abs(i-j)][w] for j,w in assigned.items())]
   if not allowed:return
   if vals is None or len(allowed)<len(vals):best=i;vals=allowed
  for v in vals:assigned[best]=v;dfs(assigned,unused-{v});del assigned[best]
 try:dfs({},set(range(1,k+1)));complete=True
 except RuntimeError:complete=False
 print(json.dumps({'k':k,'count':count,'nodes':nodes,'complete':complete,'no_endpoint_1':noendpoint,'scope':'complete permutation domain with pairwise gcd compatibility; auxiliary endpoint diagnostic only'}),flush=True)
