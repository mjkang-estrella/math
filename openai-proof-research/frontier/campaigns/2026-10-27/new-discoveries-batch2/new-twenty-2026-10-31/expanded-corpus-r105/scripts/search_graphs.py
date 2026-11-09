import numpy as np, itertools,random,json,pathlib,sys,time
D=pathlib.Path(__file__).resolve().parents[1];random.seed(105)
def calc(n,edges):
 A=np.zeros((n,n)); adj=[[] for _ in range(n)]
 for u,v in edges:A[u,v]=A[v,u]=1;adj[u].append(v);adj[v].append(u)
 dist=[]
 for s in range(n):
  d=[n]*n;d[s]=0;q=[s]
  for u in q:
   for v in adj[u]:
    if d[v]==n:d[v]=d[u]+1;q.append(v)
  if len(q)<n:return
  dist.append(d)
 deg=A.sum(axis=1); vals=[]
 for a in [1,0,-1]:
  c=(deg**a)*(A@(deg**(-a)));ev=np.linalg.eigvalsh(np.diag(c)-A);vals.append(n*sum(1/x for x in ev[1:]))
 sz=0
 for u,v in edges:
  nu=sum(dist[u][w]<dist[v][w] for w in range(n));nv=sum(dist[v][w]<dist[u][w] for w in range(n));sz+=nu*nv*int(deg[u]+deg[v])
 bound=n*(n//2)**2*((n+1)//2)**2
 return vals,sz,bound
mode=sys.argv[1];counts={};bad=[];mins=[1e100,1e100];mx=0
ns=range(2,7) if mode=='small' else [9,10,12,16,24,40]
for n in ns:
 pairs=list(itertools.combinations(range(n),2));ct=0
 seq=range(1<<len(pairs)) if mode=='small' else range(1500)
 for mask in seq:
  if mode=='small':edges=[e for i,e in enumerate(pairs) if mask>>i&1]
  else:
   p=random.choice([.08,.15,.25,.4,.6,.8,.95]);edges=[e for e in pairs if random.random()<p]
  z=calc(n,edges)
  if z is None:continue
  ct+=1;v,s,b=z;gaps=[v[0]-v[1],v[1]-v[2]];mins=[min(x,y) for x,y in zip(mins,gaps)];mx=max(mx,s/b)
  if min(gaps)<-1e-6 or s>b:bad.append(dict(n=n,edges=edges,kirchhoff=v,sz=s,bound=b));print('BAD',bad[-1],flush=True);break
 counts[n]=ct;print(n,ct,mins,mx,flush=True)
(D/f'outputs/graphs-{mode}.json').write_text(json.dumps(dict(counts=counts,min_float_gaps=mins,max_sz_bound_ratio=mx,candidates=bad),indent=2))
