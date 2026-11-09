import pathlib,json,sys,itertools,math,time
D=pathlib.Path(__file__).resolve().parents[1]
mode=sys.argv[1]
if mode=='mobius':
 N=int(sys.argv[2]);spf=list(range(N+2))
 for p in range(2,math.isqrt(N+1)+1):
  if spf[p]==p:
   for j in range(p*p,N+2,p):
    if spf[j]==j:spf[j]=p
 def fac(n):
  f={}
  while n>1:p=spf[n];f[p]=f.get(p,0)+1;n//=p
  return f
 mu=[0]*(N+1);mu[1]=1;records=[];best=0
 for n in range(2,N+1):
  f=fac(n);g=fac(n+1)
  for p,e in g.items():f[p]=f.get(p,0)+e
  f[2]-=1;ds=[1]
  for p,e in f.items():ds=[d*p**a for d in ds for a in range(e+1)]
  val=0
  for d in ds:
   r=math.isqrt(8*d+1)
   if r*r==8*d+1:
    j=(r-1)//2
    if j<n:val-=mu[j]
  mu[n]=val
  if abs(val)>best:best=abs(val);records.append([n,val])
 print(json.dumps({'N':N,'record_magnitudes':records,'maximum':best,'tail':mu[-20:]}))
elif mode=='irregular':
 import networkx as nx
 total=0;decomp=0;fail=[];nodes=0
 for G in nx.graph_atlas_g():
  n=len(G);es=list(G.edges());m=len(es)
  if n<2 or not nx.is_connected(G) or m>int(sys.argv[2]):continue
  total+=1;deg=[[0]*n for _ in range(4)];groups=[[] for _ in range(4)]
  es.sort(key=lambda e:-(G.degree(e[0])+G.degree(e[1])))
  def dfs(j,used):
   global nodes
   nodes+=1
   if j==m:return all(all(deg[c][u]!=deg[c][v] for u,v in groups[c]) for c in range(used))
   u,v=es[j]
   for c in range(min(used+1,4)):
    deg[c][u]+=1;deg[c][v]+=1;groups[c].append((u,v))
    if dfs(j+1,max(used,c+1)):return True
    groups[c].pop();deg[c][u]-=1;deg[c][v]-=1
   return False
  ok=dfs(0,0)
  if ok:decomp+=1
  else:fail.append({'n':n,'edges':es})
 print(json.dumps({'connected_atlas_order_at_most':7,'edge_cap':int(sys.argv[2]),'graphs':total,'four_decomposable':decomp,'failures_require_decomposability_classification':fail,'dfs_nodes':nodes}))
elif mode=='eigen':
 import numpy as np
 rng=np.random.default_rng(224);records=[]
 for n in range(4,9):
  best=(-1e9,None)
  for j in range(1000):
   X=rng.integers(-3,4,(n,n))+1j*rng.integers(-3,4,(n,n));X=X/np.linalg.norm(X)
   A=np.kron(np.eye(n),X)-np.kron(X.T,np.eye(n));ev=np.linalg.eigvalsh(A.conj().T@A)[::-1]
   gaps=np.cumsum(ev)[1::2]-np.arange(4,4+2*(len(ev)//2),2)
   k=int(np.argmax(gaps))
   if gaps[k]>best[0]:best=(float(gaps[k]),k+1)
  records.append({'n':n,'samples':1000,'largest_numeric_violation':best})
 print(json.dumps(records))
