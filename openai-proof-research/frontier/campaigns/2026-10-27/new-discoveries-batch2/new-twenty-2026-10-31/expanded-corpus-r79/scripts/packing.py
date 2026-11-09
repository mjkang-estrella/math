import pathlib,sys,json,itertools as it
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'deps'));import networkx as nx
out=[]
for G in nx.graph_atlas_g():
 n=len(G);m=len(G.edges)
 if not 2<=n<=5 or m<n-1 or m>5:continue
 N=2*m+1;vs=sorted(G,key=lambda v:-G.degree(v));a={vs[0]:0};nodes=[0]
 def rec(j,diffs):
  nodes[0]+=1
  if nodes[0]>100000:return None
  if j==n:return a.copy()
  v=vs[j]
  for x in range(1,N):
   if x in a.values():continue
   ds=[min((x-a[u])%N,(a[u]-x)%N) for u in G[v] if u in a]
   if len(set(ds))==len(ds) and set(ds).isdisjoint(diffs):
    a[v]=x;r=rec(j+1,diffs|set(ds))
    if r is not None:return r
    del a[v]
  return None
 w=rec(1,set());out.append({'graph6':nx.to_graph6_bytes(G,header=False).decode().strip(),'n':n,'m':m,'nodes':nodes[0],'cyclic_witness':w,'outcome':'cyclic decomposition witness' if w else 'no cyclic witness; not nonpacking'})
(D/'outputs/search-351080.json').write_text(json.dumps({'scope':'all graph atlas graphs 2<=n<=5 and n-1<=m<=5; searches injective vertex images in Z_(2m+1) with each undirected difference1..m exactly once; 100000nodes cap each. This constructs cyclic decompositions but cannot refute unrestricted asymptotic conjecture.','cases':out},indent=2)+'\n')
# All families of unrooted trees orders1..6, packing into K_n.
res=[]
for n in range(2,7):
 trees={r:list(nx.nonisomorphic_trees(r)) for r in range(2,n+1)};pairs=list(it.combinations(range(n),2));ix={e:j for j,e in enumerate(pairs)};cnt=0;failed=[]
 def embeddings(G):
  masks=set()
  for p in it.permutations(range(n),len(G)):
   M=0
   for a,b in G.edges:M|=1<<ix[tuple(sorted((p[a],p[b]))) ]
   masks.add(M)
  return sorted(masks)
 E={r:[embeddings(G) for G in trees[r]] for r in trees}
 for family in it.product(*[range(len(trees[r])) for r in range(2,n+1)]):
  lists=[E[r][family[r-2]] for r in range(n,1,-1)]
  def rec(j,used):
   if j==len(lists):return True
   return any(rec(j+1,used|M) for M in lists[j] if not used&M)
  cnt+=1
  if not rec(0,0):failed.append(family)
 res.append({'n':n,'families':cnt,'failures':failed})
 (D/'outputs/search-365380.json').write_text(json.dumps({'scope':'all tuples of unrooted tree isomorphism classes T2..Tn for n2..6; all injective vertex embeddings in K_n searched by edge bitmask exact cover','cases':res},indent=2)+'\n')
