import json,pathlib,math
D=pathlib.Path(__file__).resolve().parents[1];B=128
primes={p for p in range(2,B) if all(p%d for d in range(2,math.isqrt(p)+1))};compat=[sum(1<<b for b in range(B) if abs(a-b) in primes) for a in range(B)];out=[]
for n,k in [(15,4),(15,5),(15,6),(16,2),(16,4),(16,6),(17,4),(17,5),(17,6)]:
 adj=[{(v+d)%n for d in [1,-1,k,-k]} for v in range(n)];labels=[-1]*n;labels[0]=0;nodes=0;cap=200000
 def dfs(used):
  global nodes
  nodes+=1
  if nodes>cap:return False
  best=None
  for v in range(n):
   if labels[v]>=0:continue
   allowed=((1<<B)-1)&~used
   for w in adj[v]:
    if labels[w]>=0:allowed&=compat[labels[w]]
   score=(allowed.bit_count(),-sum(labels[w]>=0 for w in adj[v]))
   if best is None or score<best[0]:best=(score,v,allowed)
  if best is None:return True
  _,v,opts=best
  while opts:
   bit=opts&-opts;opts-=bit;labels[v]=bit.bit_length()-1
   if dfs(used|bit):return True
   labels[v]=-1
   if nodes>cap:return False
  return False
 success=dfs(1)
 if success:assert len(set(labels))==n and all(abs(labels[v]-labels[w]) in primes for v in range(n) for w in adj[v])
 row=dict(n=n,k=k,label_window=[0,B-1],fixed_label_vertex0=0,nodes=nodes,cap=cap,success=success,labels=labels if success else None,exhausted_window=not success and nodes<=cap);out.append(row);print(row,flush=True);(D/'outputs/prime-distance.json').write_text(json.dumps(out,indent=2))
