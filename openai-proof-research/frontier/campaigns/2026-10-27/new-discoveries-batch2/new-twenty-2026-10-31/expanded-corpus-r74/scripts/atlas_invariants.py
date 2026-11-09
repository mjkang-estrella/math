import os,resource,pathlib,itertools,json,math,random
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);import networkx as nx
D=pathlib.Path(__file__).resolve().parents[1]
def eigs(A):
 A=[list(map(float,r)) for r in A];n=len(A)
 for _ in range(500*n*n):
  _,p,q=max((abs(A[i][j]),i,j) for i in range(n) for j in range(i))
  if abs(A[p][q])<1e-12:break
  tau=(A[q][q]-A[p][p])/(2*A[p][q]);t=(1 if tau>=0 else -1)/(abs(tau)+math.sqrt(1+tau*tau));c=1/math.sqrt(1+t*t);s=t*c;app=A[p][p];aqq=A[q][q];apq=A[p][q]
  A[p][p]=app-t*apq;A[q][q]=aqq+t*apq;A[p][q]=A[q][p]=0
  for k in range(n):
   if k not in [p,q]:a=A[k][p];b=A[k][q];A[k][p]=A[p][k]=c*a-s*b;A[k][q]=A[q][k]=s*a+c*b
 return sorted([A[i][i] for i in range(n)],reverse=True)
def det(A):
 A=[r[:] for r in A];n=len(A);prev=1;sgn=1
 for k in range(n-1):
  if A[k][k]==0:
   j=next((j for j in range(k+1,n) if A[j][k]),None)
   if j is None:return 0
   A[k],A[j]=A[j],A[k];sgn=-sgn
  pivot=A[k][k]
  for i in range(k+1,n):
   for j in range(k+1,n):A[i][j]=(A[i][j]*pivot-A[i][k]*A[k][j])//prev
  prev=pivot
 return sgn*A[-1][-1]
def tau(G):
 n=len(G);return det([[G.degree(i) if i==j else -int(G.has_edge(i,j)) for j in range(n-1)] for i in range(n-1)])
def chrom(G):
 n=len(G);order=sorted(G,key=lambda v:-G.degree(v));col={}
 def rec(z,k):
  if z==n:return True
  v=order[z];bad={col[u] for u in G[v] if u in col}
  for c in range(k):
   if c not in bad:
    col[v]=c
    if rec(z+1,k):return True
    del col[v]
  return False
 for k in range(1,n+1):
  if rec(0,k):return k
counts={'spectral_noncomplete':0,'Reed_graphs':0,'distance_regular':0};bad=[];spanning={}
for idx,G in enumerate(nx.graph_atlas_g()):
 n=len(G)
 if n<2:continue
 m=G.number_of_edges();omega=max(map(len,nx.find_cliques(G)));delta=max(dict(G.degree()).values());chi=chrom(G);counts['Reed_graphs']+=1
 if chi>math.ceil((omega+delta+1)/2):bad.append({'id':379837,'atlas':idx})
 if m<n*(n-1)//2:
  ev=eigs([[int(G.has_edge(i,j)) for j in range(n)] for i in range(n)]);counts['spectral_noncomplete']+=1
  if ev[0]**2+ev[1]**2>2*m*(omega-1)/omega+1e-8:bad.append({'id':379969,'atlas':idx,'eigenvalues':ev})
 if not nx.is_connected(G):continue
 st=tau(G);key=f'{n},{m}';spanning[key]=max(spanning.get(key,0),st)
 if len(set(dict(G.degree()).values()))!=1:continue
 dist=dict(nx.all_pairs_shortest_path_length(G));regular=True;parameters={}
 for x in G:
  for y in G:
   d=dist[x][y];v=tuple(sum(dist[x][z]==d+j for z in G[y]) for j in [-1,0,1])
   if d in parameters and parameters[d]!=v:regular=False;break
   parameters[d]=v
  if not regular:break
 if not regular:continue
 counts['distance_regular']+=1;degree=G.degree(0);h=min(sum(((mask>>u)&1)!=((mask>>v)&1) for u,v in G.edges())/(degree*mask.bit_count()) for mask in range(1,1<<n) if mask.bit_count()<=n//2);ev=eigs([[int(G.has_edge(i,j)) for j in range(n)] for i in range(n)]);lam=1-ev[1]/degree
 if h>lam+1e-8 or h<lam/2-1e-8:bad.append({'id':381430,'atlas':idx,'h':h,'lambda':lam})
random.seed(74);samples=[];G=nx.petersen_graph();best=tau(G)
for i in range(20000):
 H=nx.gnm_random_graph(10,15,seed=random.randrange(1<<32))
 if nx.is_connected(H):
  t=tau(H)
  if t>best:best=t;samples.append({'sample':i,'trees':t,'edges':list(H.edges())})
out={'ids':[379837,379969,381430,380808],'space':'all unlabeled simple graphs orders2..7 in NetworkX atlas; connected and distance-regular filters as applicable','counts':counts,'counterexamples':bad,'spectral_limit':'Floating point Jacobi diagonalization, tolerance1e-8; diagnostics, not exact spectral certificates','maximum_spanning_tree_counts_by_n_m':spanning,'Petersen_random_comparisons':20000,'seed':74,'Petersen_tree_count':tau(G),'improvements':samples};(D/'outputs/atlas-invariants.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
