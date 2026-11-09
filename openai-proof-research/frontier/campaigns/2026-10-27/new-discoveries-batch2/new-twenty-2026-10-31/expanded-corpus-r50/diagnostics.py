import resource
resource.setrlimit(resource.RLIMIT_AS,(3*1024**3,3*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(100,100))
import numpy as np,json,pathlib,time
class NX:
 def to_numpy_array(self,g):return g
 def path_graph(self,n):
  a=np.zeros((n,n));
  for i in range(n-1):a[i,i+1]=a[i+1,i]=1
  return a
 def lollipop_graph(self,r,s):
  a=self.path_graph(r+s);a[:r,:r]=1-np.eye(r);return a
 def barbell_graph(self,r,s):
  a=self.path_graph(2*r+s);a[:r,:r]=1-np.eye(r);a[-r:,-r:]=1-np.eye(r);return a
 def gnp_random_graph(self,n,p,seed):
  a=np.triu(np.random.default_rng(seed).random((n,n))<p,1);return (a+a.T).astype(float)
 def is_connected(self,a):
  seen={0};todo=[0]
  while todo:
   for j in np.where(a[todo.pop()])[0]:
    if j not in seen:seen.add(j);todo.append(j)
  return len(seen)==len(a)
 def to_graph6_bytes(self,g,header=False):return json.dumps([[int(u),int(v)] for u,v in zip(*np.where(np.triu(g,1)))]).encode()
nx=NX()
p=pathlib.Path(__file__).resolve().parent;rng=np.random.default_rng(501);start=time.time();res=[]
def derivatives(g):
 a=nx.to_numpy_array(g);d=a.sum(1);m=d.sum()/2;n=len(d);j=np.ones((n,n))/n;l=np.linalg.inv(np.diag(d)-a+j)-j;r=np.diag(l)[:,None]+np.diag(l)[None,:]-2*l;k=d@r@d/(4*m);rd=r@d
 vals=[]
 for u in range(n):
  for v in range(u+1,n):
   z=l[:,u]-l[:,v];ds=rd[u]+rd[v]-2*m*(d@(z*z))+(d@z)**2;vals.append((ds/(2*m)-k/m,u,v))
 return vals
for n in range(8,25):
 best=max((max(derivatives(nx.lollipop_graph(r,n-r))),r) for r in range(2,n-1));target=best[0][0];pathmin=min(derivatives(nx.path_graph(n)))[0];hi=(-1e9,None);lo=(1e9,None)
 graphs=[nx.barbell_graph(r,n-2*r) for r in range(2,n//2+1) if n-2*r>=0]
 for _ in range(100):
  g=nx.gnp_random_graph(n,float(rng.uniform(.08,.8)),seed=int(rng.integers(2**31)))
  if nx.is_connected(g):graphs.append(g)
 for g in graphs:
  vals=derivatives(g);e=max(x for x in vals if g[x[1],x[2]]);ne=[x for x in vals if not g[x[1],x[2]]]
  if e[0]>hi[0]:hi=(e[0],nx.to_graph6_bytes(g,header=False).decode().strip())
  if ne and min(ne)[0]<lo[0]:lo=(min(ne)[0],nx.to_graph6_bytes(g,header=False).decode().strip())
 row={'n':n,'lollipop_max':target,'lollipop_r':best[1],'path_end_min':pathmin,'sample_edge_max':hi,'sample_nonedge_min':lo,'graphs':len(graphs)};res.append(row);print(row,flush=True)
 if hi[0]>target+1e-7 or lo[0]<pathmin-1e-7:print('POTENTIAL_COUNTEREXAMPLE',flush=True)
(p/'kemeny-diagnostic.json').write_text(json.dumps(res,indent=2));print('elapsed',time.time()-start)
