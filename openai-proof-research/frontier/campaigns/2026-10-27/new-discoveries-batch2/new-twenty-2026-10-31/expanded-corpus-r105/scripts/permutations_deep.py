import itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1]
def stack(p):
 if not p:return ()
 k=p.index(max(p));return stack(p[:k])+stack(p[k+1:])+(p[k],)
def av321(p):
 return not any(p[i]>p[j]>p[k] for i in range(len(p)) for j in range(i+1,len(p)) for k in range(j+1,len(p)))
def lis(p):
 d=[]
 import bisect
 for x in p:
  i=bisect.bisect_left(d,x)
  if i==len(d):d.append(x)
  else:d[i]=x
 return len(d)
cat={0:[()]};a321=[()];out=[]
for n in range(1,15):
 cat[n]=[tuple(x+n-k for x in l)+(n,)+r for k in range(1,n+1) for l in cat[k-1] for r in cat[n-k]]
 a321=[q[:i]+(n,)+q[i:] for q in a321 for i in range(n) if all(q[j]<q[j+1] for j in range(i,len(q)-1))]
 rhs=[sum(lis(p)<=t+1 for p in cat[n]) for t in range(1,n+1)];counts=[]
 for ps in [[tuple(n+1-x for x in reversed(p)) for p in cat[n]],a321]:
  dist=[0]*(n+1)
  for p in ps:
   t=0
   while p!=tuple(range(1,n+1)):p=stack(p);t+=1
   for j in range(max(1,t),n+1):dist[j]+=1
  counts.append(dist[1:])
 z=dict(n=n,objects_per_class=len(a321),rhs=rhs,p213=counts[0],p321=counts[1],holds=rhs==counts[0]==counts[1]);out.append(z);print(z,flush=True);(D/'outputs/permutations-deep.json').write_text(json.dumps(out,indent=2))
