import numpy as np, networkx as nx,json,itertools as it,time
s=time.monotonic();tol=1e-7
def span(M):
 u,v,_=np.linalg.svd(M,full_matrices=False)
 return u[:,v>tol]
def qp(G):
 A=nx.to_numpy_array(G);n=len(A)
 vals,vec=np.linalg.eigh(A);spaces=[]
 for val in vals:
  if not spaces or abs(val-spaces[-1][0])>tol:spaces.append([val,[]])
 for val,Q in spaces:
  Q.extend(np.where(abs(vals-val)<tol)[0])
 eig=[vec[:,Q] for _,Q in spaces];one=np.ones((n,1))/n**.5
 # choose nonconstant eigenspace as V1, then the product filtration determines subsequent spaces.
 orders=[]
 for k,V in enumerate(eig):
  if abs(float(np.linalg.norm(V.T@one))-1)<tol:continue
  W=one;used={len(eig)-1};order=[]
  for step in range(1,len(eig)):
   W2=span(np.column_stack([W]+[(W[:,i,None]*V) for i in range(W.shape[1])]))
   new=[j for j,E in enumerate(eig) if j not in used and np.linalg.norm(E-W2@(W2.T@E))<tol]
   if len(new)!=1:break
   j=new[0]
   if W2.shape[1]!=W.shape[1]+eig[j].shape[1]:break
   used.add(j);order.append(j);W=W2
  else:
   if W.shape[1]==n:orders.append(order)
 if not orders:return False,False
 # Span of spectral idempotents is M; check entrywise products.
 Es=[E@E.T for E in eig];B=span(np.column_stack([E.ravel() for E in Es]))
 closed=all(np.linalg.norm((E*F).ravel()-B@(B.T@(E*F).ravel()))<tol for E in Es for F in Es)
 return True,closed
gs=[G for G in nx.graph_atlas_g() if len(G)>1 and nx.is_connected(G) and len(set(dict(G.degree()).values()))==1]
counts={}
for G in gs:
 yes,closed=qp(G);key=str(len(G));c=counts.setdefault(key,dict(graphs=0,qpoly=0,failures=0))
 c['graphs']+=1;c['qpoly']+=yes;c['failures']+=yes and not closed
print(json.dumps(dict(atlas=counts,seconds=time.monotonic()-s)),flush=True)
rng=np.random.default_rng(149);tot=q=fail=0
for n in [8,10,12,14,16]:
 for d in range(2,min(n-1,7)+1):
  for j in range(20):
   G=nx.random_regular_graph(d,n,seed=int(rng.integers(1000000000)))
   if not nx.is_connected(G):continue
   yes,closed=qp(G);tot+=1;q+=yes;fail+=yes and not closed
 print(json.dumps(dict(through_n=n,samples=tot,qpoly=q,failures=fail,seconds=time.monotonic()-s)),flush=True)
