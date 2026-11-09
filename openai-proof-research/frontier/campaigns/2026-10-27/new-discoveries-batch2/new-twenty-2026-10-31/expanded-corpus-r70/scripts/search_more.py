import networkx as nx,itertools,pathlib,json
D=pathlib.Path(__file__).resolve().parents[1];out={}
def colorable(adj,k):
 colors={}
 def go():
  if len(colors)==len(adj):return True
  u=max((v for v in adj if v not in colors),key=lambda v:(len({colors[w] for w in adj[v] if w in colors}),len(adj[v])))
  used={colors[v] for v in adj[u] if v in colors}
  for c in range(min(k,1+max(colors.values(),default=-1)+1)):
   if c not in used:
    colors[u]=c
    if go():return True
    del colors[u]
  return False
 return go()
rows=[]
for G in nx.graph_atlas_g():
 n=len(G)
 if n<2 or not nx.is_connected(G):continue
 L=nx.line_graph(G);Delta=max(dict(G.degree()).values());adj={u:set(L[u])|{w for v in L[u] for w in L[v] if w!=u} for u in L};bound=5*Delta**2//4 if Delta%2==0 else (5*Delta**2-2*Delta+1)//4
 assert colorable(adj,bound)
 if len(rows)<995:rows.append(n)
 if all(d==3 for _,d in G.degree()) and n>4:
  pairs=list(itertools.combinations(range(8),2));edge=list(L);col={}
  def tone():
   if len(col)==len(edge):return True
   u=max((u for u in edge if u not in col),key=lambda u:sum(v in col for v in adj[u]))
   for p in pairs:
    if all((not(set(p)&set(col[v])) if v in L[u] else p!=col[v]) for v in adj[u] if v in col):
     col[u]=p
     if tone():return True
     del col[u]
   return False
  assert tone();out.setdefault('374909',[]).append(nx.to_graph6_bytes(G,header=False).decode().strip())
 if nx.is_biconnected(G):
  # No full extremal conclusion: sufficiently-large n not fixed; record available maxima with no forbidden cycle for k=3,4.
  lengths={len(c) for c in nx.simple_cycles(G)}
  for k in [3,4]:
   if not any(l%(2*k)==2 for l in lengths):
    out.setdefault('375062',{}).setdefault(f'{k},{n}',0);out['375062'][f'{k},{n}']=max(out['375062'][f'{k},{n}'],G.number_of_edges())
 if n>=6 and nx.check_planarity(G)[0] and G.number_of_edges()==3*n-6 and nx.node_connectivity(G)>=4:
  # perfect matchings via recursive exact branching
  def pm(S):
   if not S:return 1
   u=min(S);return sum(pm(S-{u,v}) for v in G[u] if v in S)
  out.setdefault('375481',[]).append(dict(n=n,perfect_matchings=pm(set(G))))
out['375116']={'connected_atlas_graphs':len(rows),'orders':'2..7','counterexamples':[]}
# NF fixed vertex set antichain transform. Return up to vertex permutations, no operator shortcut.
nf=[]
for n in range(2,5):
 for m in range(n,5):
  N=n+m;U=(1<<N)-1
  F={ (1<<i)|(1<<j) for i in range(n) for j in range(i+1,n)}|{(1<<i)|(1<<j) for i in range(n,N) for j in range(i+1,N)}|{1|(1<<n)};orig=F.copy();period=None
  for step in range(1,N+4):
   allowed=[s for s in range(1<<N) if all(s&f!=f for f in F)]
   F={s for s in allowed if all((s|(1<<i)) not in allowed for i in range(N) if not s>>i&1)}
   if len(F)==len(orig) and all(s.bit_count()==2 for s in F):
    A=nx.Graph();A.add_nodes_from(range(N));A.add_edges_from(tuple(i for i in range(N) if s>>i&1) for s in F)
    B=nx.Graph();B.add_nodes_from(range(N));B.add_edges_from(tuple(i for i in range(N) if s>>i&1) for s in orig)
    if nx.is_isomorphic(A,B):period=step;break
  nf.append(dict(n=n,m=m,first_return_up_to_isomorphism=period,predicted=2 if n==m==2 else N+2))
out['375018']=nf
(D/'outputs/more.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
