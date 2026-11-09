import sys,pathlib,json,math,time,itertools
D=pathlib.Path(__file__).resolve().parents[1]
sys.path.insert(0,str(D.parent/'expanded-corpus-r99/deps'))
import networkx as nx
import numpy as np
from scipy.optimize import linprog
mode=sys.argv[1]
if mode=='tree':
 def test(g):
  n=len(g); adj=[sum(1<<j for j in g[i]) for i in range(n)];N=1<<n;trees=[]
  for s in range(1,N):
   if sum((adj[i]&s).bit_count() for i in range(n) if s>>i&1)!=2*(s.bit_count()-1):continue
   seen=s&-s;front=seen
   while front:
    b=front&-front;front-=b;v=b.bit_length()-1;a=adj[v]&s&~seen;front|=a;seen|=a
   if seen==s:trees.append(s)
  containing=[[] for _ in range(n)]
  for s in trees:
   for i in range(n):
    if s>>i&1:containing[i].append(s)
  from functools import lru_cache
  @lru_cache(None)
  def ok(s,k):
   if not s:return True
   if not k:return False
   i=(s&-s).bit_length()-1
   for t in reversed(containing[i]):
    if t&s==t and ok(s^t,k-1):return True
   return False
  return ok(N-1,(n+2)//3)
 count={};fails=[]
 for g in nx.graph_atlas_g():
  if len(g) and nx.is_connected(g) and not sum(nx.triangles(g).values()):
   count[len(g)]=count.get(len(g),0)+1
   if not test(g):fails.append(nx.to_graph6_bytes(g,header=False).decode().strip())
 print('atlas all connected triangle-free through7',count,'fails',fails,flush=True)
 import random
 rng=random.Random(101);count={}
 for n in range(8,17):
  for rep in range(20):
   g=nx.random_tree(n,seed=rng) if hasattr(nx,'random_tree') else nx.random_labeled_tree(n,seed=rng)
   pairs=list(itertools.combinations(range(n),2));rng.shuffle(pairs)
   for i,j in pairs:
    if rng.random()<.45 and not set(g[i])&set(g[j]):g.add_edge(i,j)
   if not test(g):fails.append(nx.to_graph6_bytes(g,header=False).decode().strip());print('FAIL',n,fails[-1],flush=True)
   count[n]=count.get(n,0)+1
  print('random trianglefree',n,count[n],flush=True)
 print('all fails',fails)
elif mode=='adverse':
 count=0;integral=0;adv=[]
 graphs=[g for g in nx.graph_atlas_g() if len(g)>1 and min(dict(g.degree()).values())>0]
 graphs += [nx.petersen_graph(),nx.desargues_graph(),nx.dodecahedral_graph(),nx.icosahedral_graph(),nx.hoffman_singleton_graph()]
 for n in range(8,31,2):
  for d in range(3,min(n,9)):
   for seed in range(15):graphs.append(nx.random_regular_graph(d,n,seed=101000+n*100+d*15+seed))
 for g in graphs:
  count+=1;n=len(g);A=nx.to_numpy_array(g,nodelist=list(range(n)));ev=np.linalg.eigvalsh(A);tau=round(-ev[0])
  if abs(tau+ev[0])>1e-8 or tau==0:continue
  integral+=1
  if len(set(dict(g.degree()).values()))!=1:continue
  d=g.degree(0);v=n*tau/(d+tau)
  if abs(v-round(v))>1e-8:continue
  M=A+tau*np.eye(n);adverse=True
  for i in range(n):
   keep=[j for j in range(n) if j not in g[i]]
   if abs(np.linalg.eigvalsh(A[np.ix_(keep,keep)])[0]+tau)>1e-7:adverse=False;break
   bounds=[(0,0) if j in g[i] else (0,None) for j in range(n)]
   r=linprog(np.zeros(n),A_eq=M,b_eq=np.ones(n)*tau,bounds=bounds,method='highs')
   if not r.success:adverse=False;break
  if adverse:
   # all independent sets for n <= 26; exact maximum via complement clique routine
   alpha=max(map(len,nx.find_cliques(nx.complement(g))))
   rec={'n':n,'degree':d,'tau':tau,'upsilon':v,'alpha':alpha,'graph6':nx.to_graph6_bytes(g,header=False).decode().strip()};adv.append(rec);print('NUMERICAL_ADVERSE',rec,flush=True)
 print('tested',count,'integer least eigenvalue screens',integral,'numerical adverse',adv)
