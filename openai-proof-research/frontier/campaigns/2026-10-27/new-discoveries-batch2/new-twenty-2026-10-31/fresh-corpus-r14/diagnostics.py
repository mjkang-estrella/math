import os
os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import sys;sys.path.insert(0,'.deps')
import numpy as np, scipy.optimize as so, networkx as nx,itertools,json,time,resource,signal,random
start=time.monotonic();rng=np.random.default_rng(140333840); random.seed(140334220)
trip=np.array(list(itertools.combinations(range(6),3)))
def vectors(x):
 p=x.reshape(5,2);return np.vstack(([0,0,1],np.column_stack((np.sin(p[:,0])*np.cos(p[:,1]),np.sin(p[:,0])*np.sin(p[:,1]),np.cos(p[:,0])))))
def dets(x):return np.linalg.det(vectors(x)[trip])
theta=np.arccos(1/np.sqrt(5));ico=np.array([[theta,2*np.pi*j/5] for j in range(5)]).ravel();baseline=float(min(abs(dets(ico))))
opts=[]
for k in range(160):
 x=ico+rng.normal(0,.08,10) if k<40 else np.column_stack((rng.uniform(0,np.pi,5),rng.uniform(0,2*np.pi,5))).ravel()
 signs=np.sign(dets(x));res=so.minimize(lambda z:-z[-1],np.r_[x,min(abs(dets(x)))],constraints=[{'type':'ineq','fun':lambda z:signs*dets(z[:-1])-z[-1]}],method='SLSQP',options={'maxiter':400,'ftol':1e-11})
 opts.append({'start':k,'success':bool(res.success),'min_det':float(min(abs(dets(res.x[:-1])))),'iterations':res.nit,'x':res.x.tolist()})
json.dump({'baseline':baseline,'runs':opts,'best':max(opts,key=lambda a:a['min_det']),'elapsed_seconds':time.monotonic()-start},open('determinant-diagnostics.json','w'),indent=2)
print('determinants',baseline,max(a['min_det'] for a in opts),flush=True)
# A complete 3-color search per graph; domains propagated by missing-neighborhood colors.
def color(G):
 n=len(G);adj=[set(G[i]) for i in range(n)];nodes=0
 def dfs(c):
  nonlocal nodes;nodes+=1
  while True:
   forced=None
   for nb in adj:
    used={c[v] for v in nb if c[v]>=0};un=[v for v in nb if c[v]<0];missing=set(range(3))-used
    if len(un)<len(missing):return None
    if len(un)==1 and missing:forced=(un[0],next(iter(missing)));break
   if forced is None:break
   c=c.copy();c[forced[0]]=forced[1]
  if -1 not in c:return c
  v=max((v for v in range(n) if c[v]<0),key=lambda v:sum(1/(1+sum(c[w]<0 for w in adj[u])) for u in adj[v]))
  used=set(c)-{-1}
  for a in range(min(3,len(used)+1)):
   cc=c.copy();cc[v]=a;r=dfs(cc)
   if r is not None:return r
  return None
 c=[-1]*n;c[0]=0
 return dfs(c),nodes
def alarm(s,f):raise TimeoutError()
signal.signal(signal.SIGALRM,alarm)
records=[]
for n in range(6,31):
 G=nx.empty_graph(n);G.add_edges_from((i,2+(i-2+1)%(n-2)) for i in range(2,n));G.add_edges_from((h,i) for h in [0,1] for i in range(2,n))
 for sample in range(12):
  for step in range(12*n):
   a,b=random.choice(list(G.edges()));common=list(set(G[a])&set(G[b]))
   if len(common)!=2 or G.degree(a)<=4 or G.degree(b)<=4:continue
   c,d=common
   if G.has_edge(c,d):continue
   G.remove_edge(a,b);G.add_edge(c,d)
  signal.alarm(2)
  try: col,nodes=color(G);status='coloring' if col is not None else 'COUNTEREXAMPLE'
  except TimeoutError:col=None;nodes=None;status='timeout'
  finally:signal.alarm(0)
  records.append({'n':n,'sample':sample,'status':status,'nodes':nodes,'colors':col,'edges':list(G.edges()),'min_degree':min(dict(G.degree()).values())})
  if status=='COUNTEREXAMPLE':break
 if any(r['status']=='COUNTEREXAMPLE' for r in records):break
json.dump({'records':records,'elapsed_seconds':time.monotonic()-start,'maxrss_kb':resource.getrusage(resource.RUSAGE_SELF).ru_maxrss},open('triangulation-diagnostics.json','w'),indent=2)
print('triangulations',len(records),{s:sum(r['status']==s for r in records) for s in ['coloring','timeout','COUNTEREXAMPLE']},'seconds',time.monotonic()-start)
