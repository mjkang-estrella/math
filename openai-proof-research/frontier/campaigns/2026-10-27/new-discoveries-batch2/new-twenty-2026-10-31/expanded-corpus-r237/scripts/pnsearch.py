from pathlib import Path
import networkx as nx,json,collections,itertools,time
L=Path(__file__).resolve().parents[1]
def step(G,n):
 E=list(G.edges()); idx={frozenset(e):i for i,e in enumerate(E)}; H=nx.Graph();H.add_nodes_from(range(len(E)))
 def dfs(path):
  if len(path)==n:
   es=[idx[frozenset(e)] for e in zip(path,path[1:])]
   # all incident edges contained in same P_n, including nonconsecutive incident edges impossible on simple path
   H.add_edges_from(zip(es,es[1:]));return
  for w in G[path[-1]]:
   if w not in path:dfs(path+[w])
 for v in G:dfs([v])
 return H
def signature(G):return (len(G),G.number_of_edges(),tuple(sorted(dict(G.degree()).values())))
def converge(G,n):
 old=G;seq=[]
 for t in range(12):
  if len(old)>40 or old.number_of_edges()>70:return 'cap',t,seq
  seq.append(signature(old));H=step(old,n)
  if len(H)==0:return 'terminate',t+1,seq
  if signature(H)==signature(old) and nx.is_isomorphic(H,old):return 'converge',t+1,seq
  old=H
 return 'iteration_cap',12,seq
stats=collections.Counter();hits=[];start=time.time()
for n in range(4,9):
 for ai,G in enumerate(nx.graph_atlas_g()):
  if len(G)==0 or not nx.is_connected(G):continue
  status,t,seq=converge(G,n);stats[f'{n}:{status}']+=1
  if status!='converge':continue
  # Minimality by every edge deletion: convergence not monotone, so this is only a necessary screen.
  if any(converge(nx.Graph(G.edge_subgraph([f for f in G.edges() if set(f)!=set(e)])),n)[0]=='converge' for e in G.edges()):continue
  if G.number_of_edges()!=len(G):
   h={'atlas':ai,'n':n,'edges':list(G.edges()),'sequence':seq,'status':'minimality_candidate_only'};hits.append(h);print('HIT',h,flush=True)
 print('done',n,dict(stats),flush=True)
(L/'outputs/pnsearch.json').write_text(json.dumps({'stats':stats,'hits':hits,'wall':time.time()-start},indent=2))
