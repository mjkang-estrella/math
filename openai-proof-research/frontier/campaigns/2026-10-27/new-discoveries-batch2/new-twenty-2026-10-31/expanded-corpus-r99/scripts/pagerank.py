import os,resource,time,json,pathlib,itertools
resource.setrlimit(resource.RLIMIT_CPU,(110,110));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2])
import numpy as np,networkx as nx
from fractions import Fraction
L=pathlib.Path.cwd();mus=[.01,.1,.5,1,2,5,10,100];tested=0;bad=[]
def pr(G,mu):
 n=len(G);E=list(G.to_directed().edges());m=len(E);C=np.zeros((m,m));u=np.array([1/n/G.degree(a) for a,b in E]);
 # edge column (a,b) moves to edge (b,c); project onto edge tails as paper T
 for i,(a,b) in enumerate(E):
  for j,(c,d) in enumerate(E):
   if b==c:C[j,i]=(mu if d==a else 1)/(G.degree(b)-1+mu)
 y=np.linalg.solve(np.eye(m)-.85*C,.15*u)
 return np.array([sum(y[j] for j,(a,b) in enumerate(E) if a==v) for v in range(n)])
for G in nx.graph_atlas_g():
 n=len(G)
 if n<3 or not nx.is_connected(G):continue
 tested+=1;p=np.array([pr(G,x) for x in mus]);d=np.diff(p,axis=0)
 for v in range(n):
  if d[:,v].min() < -1e-8 and d[:,v].max()>1e-8:
   bad.append({'n':n,'edges':list(G.edges()),'node':v,'mus':mus,'values':p[:,v].tolist(),'min_degree':min(dict(G.degree()).values())});break
 if len(bad)>=30:break
print(json.dumps({'tested_connected_atlas':tested,'found':bad},indent=2));(L/'outputs/pagerank.json').write_text(json.dumps({'tested':tested,'found':bad},indent=2))
