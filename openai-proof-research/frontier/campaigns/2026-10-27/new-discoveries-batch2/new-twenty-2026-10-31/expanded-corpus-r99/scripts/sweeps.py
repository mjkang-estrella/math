import os,resource,sys,json,time,math,itertools
resource.setrlimit(resource.RLIMIT_CPU,(115,115));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
import networkx as nx
mode=sys.argv[1];out={'mode':mode,'start':time.time(),'coverage':[],'counterexamples':[]}
def save():
 out['seconds']=time.time()-out['start'];json.dump(out,open('outputs/'+mode+'.json','w'),indent=2)
if mode=='square':
 N=200000
 for n in range(6,101):
  a=[0]*(N+1);a[0]=1
  for k in range(1,n+1):
   for x in range(k,N+1):a[x]+=a[x-k]
  hits=[(x,math.isqrt(a[x])) for x in range(2,N+1) if math.isqrt(a[x])**2==a[x]]
  out['coverage'].append({'n':n,'x':[2,N],'hits':hits});save()
  if time.time()-out['start']>100:break
elif mode=='jets':
 for G in nx.graph_atlas_g():
  n=len(G)
  if n<2 or n%2 or any(d==0 for v,d in G.degree()):continue
  sizes={len(c)for c in nx.find_cliques(nx.complement(G))}
  if sizes!={n//2}:continue
  for s in range(1,7):
   H=nx.Graph();H.add_nodes_from(itertools.product(range(n),range(s+1)))
   H.add_edges_from(((a,i),(b,j))for a,b in G.edges()for i in range(s+1)for j in range(s+1-i))
   sz={len(c)for c in nx.find_cliques(nx.complement(H))};out['coverage'].append({'graph6':nx.to_graph6_bytes(G,header=False).decode().strip(),'n':n,'s':s,'maximal_independent_sizes':sorted(sz)})
   if sz!={n*(s+1)//2}:out['counterexamples'].append(out['coverage'][-1])
   save()
elif mode=='toughness':
 for G in nx.graph_atlas_g():
  n=len(G)
  if n<3:continue
  if any(nx.number_connected_components(G.subgraph([v for v in G if not(mask>>v&1)]))>mask.bit_count()/2+1 for mask in range(1<<n)):continue
  E=list(G.edges());found=False
  # Hamiltonian cycles first, fixing vertex 0 and reversal
  for perm in itertools.permutations(range(1,n)):
   if perm[0]>perm[-1]:continue
   path=(0,)+perm+(0,)
   if all(G.has_edge(a,b)for a,b in zip(path,path[1:])):found=True;break
  if not found:
   for mask in range(1<<len(E)):
    deg=[0]*n;es=[]
    for i,(a,b)in enumerate(E):
     if mask>>i&1:deg[a]+=1;deg[b]+=1;es.append((a,b))
    if all(d in (2,4)for d in deg):
     H=nx.Graph();H.add_nodes_from(range(n));H.add_edges_from(es)
     if nx.is_connected(H):found=True;break
  out['coverage'].append({'graph6':nx.to_graph6_bytes(G,header=False).decode().strip(),'n':n,'factor':found})
  if not found:out['counterexamples'].append(out['coverage'][-1])
  save()
elif mode=='peak':
 import numpy as np
 for r in range(2,21):
  A=[1];B=[1]
  for n in range(1,81):
   A=[(r*k+1)*(A[k]if k<len(A)else 0)+r*(n-k)*(A[k-1]if k else 0) for k in range(n)]
   B=[r*k*(B[k]if k<len(B)else 0)+(r*(n-k)+1)*(B[k-1]if k else 0)for k in range(n+1)]
   P=[0]*(2*n+1)
   for k,a in enumerate(A):P[2*k+1]+=a
   for k,b in enumerate(B):P[2*k]+=b
   T=[P[0]]
   for k in range(1,len(P)):T.append(P[k]-T[-1])
   while T and T[-1]==0:T.pop()
   # zero root is allowed by source weak Hurwitz definition
   roots=np.polynomial.polynomial.polyroots(np.array(T,dtype=float)/max(T));mx=max(z.real for z in roots)
   out['coverage'].append({'r':r,'n':n,'max_real_numeric':float(mx)})
   if mx>1e-5:out['counterexamples'].append(out['coverage'][-1])
   save()
save();print(json.dumps({k:v for k,v in out.items()if k!='coverage'},indent=2));print('coverage records',len(out['coverage']))
