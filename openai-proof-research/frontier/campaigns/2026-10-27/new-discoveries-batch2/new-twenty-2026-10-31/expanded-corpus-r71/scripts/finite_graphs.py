import networkx as nx,itertools as it,math,json,pathlib,collections
D=pathlib.Path(__file__).resolve().parents[1]; stats={}
def rec(i,domain,test,w=None):
 a=stats.setdefault(str(i),{'domain':domain,'tested':0,'violations':[]});a['tested']+=1
 if not test:a['violations'].append(w)
def chi(G):
 vs=sorted(G,key=G.degree,reverse=True); col={}
 def go(j,k):
  if j==len(vs):return True
  v=vs[j];bad={col[w] for w in G[v] if w in col}
  for c in range(k):
   if c not in bad:
    col[v]=c
    if go(j+1,k):return True
    del col[v]
  return False
 return next(k for k in range(1,len(G)+1) if go(0,k))
def independent(G):return [s for k in range(len(G)+1) for s in it.combinations(G,k) if not G.subgraph(s).number_of_edges()]
def hamilton_cycles(G):
 n=len(G)
 if n<3:return []
 return [(0,)+p for p in it.permutations(range(1,n)) if p[0]<p[-1] and all(G.has_edge(a,b) for a,b in zip((0,)+p,p+(0,)))]
for G in nx.graph_atlas_g():
 n=len(G)
 if not n:continue
 m=G.number_of_edges(); deg=[d for v,d in G.degree()]; delta=max(deg); omega=max(map(len,nx.find_cliques(G))); ch=chi(G); g6=nx.to_graph6_bytes(G,header=False).decode().strip();inds=independent(G);alpha=max(map(len,inds))
 rec(375866,'All unlabelled simple graphs, orders 1..7',ch<=math.ceil((delta+1+omega)/2),g6)
 rec(376009,'All unlabelled simple graphs, orders 1..7; no eligible maximum degree >=9',True)
 L=nx.line_graph(G);L2=nx.power(L,2) if len(L) else L;wc=max(map(len,nx.find_cliques(L2)),default=0)
 rec(375753,'All unlabelled simple graphs, orders 1..7',4*wc<=5*delta**2,g6)
 L3=nx.power(L,3) if len(L) else L
 if nx.density(L3)==1 or m<=1:rec(375755,'All unlabelled simple graphs, orders 1..7; edge distance is line-graph distance',m<delta**3-delta**2+delta+2,g6)
 if nx.is_connected(G):
  if n>=2:
   ds=sorted(deg);a=max(k for k in range(n+1) if sum(ds[:k])<=m);r=deg[:]
   while max(r,default=0)>0:
    r.sort(reverse=True);d=r.pop(0)
    for j in range(d):r[j]-=1
   R=len(r);rec(375646,'All connected unlabelled simple graphs, orders 2..7',delta*alpha>=a+R,{'g6':g6,'alpha':alpha,'a':a,'R':R,'Delta':delta})
  maxis=[set(s) for s in inds if len(s)==alpha];h=next(k for k in range(n+1) if any(all(set(s)&t for t in maxis) for s in it.combinations(G,k)))
  rec(376073,'Connected unlabelled simple graphs orders 1..7; computes finite h, not an asymptotic test',True);a=stats['376073'].setdefault('largest_h_by_n',{});a[n]=max(h,a.get(n,0))
  if not all(x==2 for x in deg):
   dist=dict(nx.all_pairs_shortest_path_length(G));obj=[(v,) for v in G]+list(G.edges()); signatures={s:[min(dist[s][v] for v in o) for o in obj] for s in G};md=next(k for k in range(n+1) if any(len({tuple(signatures[s][j] for s in ss) for j in range(len(obj))})==len(obj) for ss in it.combinations(G,k)))
   rec(376380,'All connected unlabelled simple graphs orders 1..7 except cycles',md<=deg.count(1)+2*(m-n+1),g6)
  if min(deg)>=3 and n<=7:
   cs=hamilton_cycles(G)
   if cs:rec(375727,'All Hamiltonian unlabelled simple graphs orders <=7 with minimum degree >=3; c=1 diagnostic',len(cs)>1 or any(len(c)>=n-1 for sub in it.combinations(G,n-1) for c in hamilton_cycles(nx.convert_node_labels_to_integers(G.subgraph(sub)))),g6)
 planar=nx.check_planarity(G)[0]
 if planar:
  fvs=next(k for k in range(n+1) if any(nx.is_forest(G.subgraph(set(G)-set(s))) for s in it.combinations(G,k) if k<n)) if m else 0
  if nx.is_bipartite(G):rec(376134,'All bipartite planar unlabelled simple graphs orders 1..7',8*fvs<=3*n,g6)
  cycles=nx.minimum_cycle_basis(G);girth=min(map(len,cycles),default=0)
  if girth:rec(376135,'All cyclic planar unlabelled simple graphs orders 1..7; g=actual girth',girth*fvs<=m,g6)
  if delta>=3:
   sq=nx.power(G,2);bound=7 if delta==3 else delta+5 if delta<=7 else 3*delta//2+1
   rec(376237,'All planar unlabelled simple graphs orders 1..7 with Delta>=3',chi(sq)<=bound,g6)
 if n<=6:
  for k in range(3,min(n+1,7)):
   for T in nx.nonisomorphic_trees(k):
    if nx.algorithms.isomorphism.GraphMatcher(G,T).subgraph_is_monomorphic():continue
    for r in range(3,k+1):
     count=sum(all(G.has_edge(a,b) for a,b in it.combinations(s,2)) for s in it.combinations(G,r));a,b=divmod(n,k-1);bound=a*math.comb(k-1,r)+math.comb(b,r)
     rec(376257,'All unlabelled simple graphs orders 1..6; all trees k=3..min(n+1,6); r=3..k',count<=bound,{'g6':g6,'k':k,'r':r})
(D/'outputs/finite-graphs.json').write_text(json.dumps(stats,indent=2)+'\n');print(json.dumps(stats,indent=2))
