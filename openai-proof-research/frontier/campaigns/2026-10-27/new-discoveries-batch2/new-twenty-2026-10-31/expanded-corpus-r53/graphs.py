import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import resource,itertools,json,pathlib,time,numpy as np
resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(80,80))
o=pathlib.Path(__file__).resolve().parent
# Every isomorphism class has a labeling with the neighbors of zero equal to 1..d.
def run(n,d):
 a=np.zeros((n,n),dtype=np.int64);deg=[d]*n;by={};total=0
 def process():
  nonlocal total
  dist=[[-1]*n for _ in range(n)];girth=n+1
  for s in range(n):
   dist[s][s]=0;par=[-1]*n;q=[s]
   for u in q:
    for v in range(n):
     if not a[u,v]:continue
     if dist[s][v]<0:dist[s][v]=dist[s][u]+1;par[v]=u;q.append(v)
     elif par[u]!=v:girth=min(girth,dist[s][u]+dist[s][v]+1)
   if len(q)!=n:return
  total+=1;ac=float(np.linalg.eigvalsh(d*np.eye(n)-a)[1]);v=by.setdefault(girth,{'count':0,'max_ac':-1})
  v['count']+=1
  if ac>v['max_ac']+1e-10:v.update(max_ac=ac,edges=[[i,j] for i in range(n) for j in range(i+1,n) if a[i,j]])
 def rec(i):
  if i==n:process();return
  av=[j for j in range(i+1,n) if deg[j]>0];k=deg[i]
  if k>len(av):return
  choices=[tuple(range(1,d+1))] if i==0 else itertools.combinations(av,k)
  for ns in choices:
   for j in ns:a[i,j]=a[j,i]=1;deg[j]-=1
   old=deg[i];deg[i]=0
   if all(deg[j]<=n-1-i for j in range(i+1,n)):rec(i+1)
   deg[i]=old
   for j in ns:a[i,j]=a[j,i]=0;deg[j]+=1
 rec(0);return {'n':n,'d':d,'connected_labelings_fixed_neighbors':total,'by_girth':by,'spectra':'floating diagnostic only'}
ans=[]
for n,d in [(6,3),(8,3),(10,3)]:
 x=run(n,d);ans.append(x);print(json.dumps(x),flush=True);(o/'graph-diagnostics.json').write_text(json.dumps(ans,indent=2)+'\n')
