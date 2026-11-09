import networkx as nx,itertools,json,pathlib
D=pathlib.Path(__file__).resolve().parents[1];out=[]
def pairs(S):
 if not S:yield [];return
 u=S[0]
 for j in range(1,len(S)):
  for tail in pairs(S[1:j]+S[j+1:]):yield [(u,S[j])]+tail
for N in range(6,11,2):
 for a in range(3,N//2+1):
  b=N-a;base=nx.disjoint_union(nx.cycle_graph(a),nx.cycle_graph(b));cyclic=0;tested=0;bad=[];petersens=0
  for M in pairs(list(range(N))):
   if any(base.has_edge(*e) for e in M):continue
   G=base.copy();G.add_edges_from(M)
   if not nx.is_connected(G):continue
   tested+=1
   # every edge cut separating cyclic subgraphs has size >=4
   ok=True
   for s in range(1,1<<(N-1)):
    S={i for i in range(N) if s>>i&1};T=set(range(N))-S
    if sum((u in S)!=(v in S) for u,v in G.edges())>=4:continue
    A=G.subgraph(S);B=G.subgraph(T)
    if nx.cycle_basis(A) and nx.cycle_basis(B):ok=False;break
   if not ok:continue
   cyclic+=1
   if nx.is_isomorphic(G,nx.petersen_graph()):petersens+=1;continue
   es=list(G.edges());ix={frozenset(e):i for i,e in enumerate(es)};pm=[]
   for P in pairs(list(range(N))):
    if all(G.has_edge(*e) for e in P):pm.append(sum(1<<ix[frozenset(e)] for e in P))
   unions={x|y for x in pm for y in pm};allmask=(1<<len(es))-1
   if not any(x|y==allmask for x in unions for y in unions):bad.append(es)
  row=dict(N=N,cycle_lengths=[a,b],connected_pairings=tested,cyclic4_pairings=cyclic,petersen_pairings=petersens,counterexamples=bad);out.append(row);print(row,flush=True)
(D/'outputs/cubic.json').write_text(json.dumps(out,indent=2)+'\n')
