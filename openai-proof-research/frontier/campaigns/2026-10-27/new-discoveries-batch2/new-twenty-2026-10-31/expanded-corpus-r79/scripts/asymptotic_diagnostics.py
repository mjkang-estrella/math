import pathlib,sys,json,itertools as it,math
D=pathlib.Path(__file__).resolve().parents[1];sys.path.insert(0,str(D/'deps'));import networkx as nx
from functools import lru_cache
mode=sys.argv[1]
def emit(i,o):(D/'outputs'/f'search-{i}.json').write_text(json.dumps(o,indent=2)+'\n')
if mode=='treewidth':
 @lru_cache(None)
 def tw(edges,n):
  if n<=1:return 0
  best=n-1
  for v in range(n):
   nei={b if a==v else a for a,b in edges if v in (a,b)};E=set(edges)|set(it.combinations(sorted(nei),2));V=[x for x in range(n) if x!=v];idx={x:j for j,x in enumerate(V)};E=tuple(sorted((idx[a],idx[b]) for a,b in E if a!=v and b!=v));best=min(best,max(len(nei),tw(E,n-1)))
  return best
 cnt=0;bad=[]
 for G in nx.graph_atlas_g():
  n=len(G)
  if not 1<=n<=6:continue
  W=tw(tuple(sorted(G.edges)),n);found=set()
  for mask in range(1,1<<n):
   H=nx.convert_node_labels_to_integers(G.subgraph([v for v in range(n) if mask>>v&1]));m=len(H)
   if len(H.edges)==m*(m-1)//2 or nx.graph_clique_number(H)<4 if hasattr(nx,'graph_clique_number') else (len(H.edges)==m*(m-1)//2 or max((len(c) for c in nx.find_cliques(H)),default=0)<4):found.add(tw(tuple(sorted(H.edges)),m))
  cnt+=1
  if not set(range(1,W+1))<=found:bad.append({'graph6':nx.to_graph6_bytes(G,header=False).decode().strip(),'tw':W,'missing_t':sorted(set(range(1,W+1))-found)})
  emit(361361,{'scope':'all atlas graphs orders1..6; exact treewidth by all elimination orders with fill; all induced subsets checked for complete-or-K4free treewidth t=1..twG. These small finite tests do not refute a sufficiently-large-treewidth assertion.','graphs':cnt,'missing':bad})
elif mode=='sequences':
 def contains(s,u):
  for pos in it.combinations(range(len(s)),len(u)):
   mp={};rev={};ok=True
   for j,x in enumerate(pos):
    a,b=u[j],s[x]
    if (a in mp and mp[a]!=b) or (b in rev and rev[b]!=a):ok=False;break
    mp[a]=b;rev[b]=a
   if ok:return True
  return False
 out=[]
 for u in [(0,1,0),(0,1,2),(0,1,2,0),(0,1,2,0,1,2)]:
  r=len(set(u))
  def sparse(s):return all(s[i]!=s[j] for i in range(len(s)) for j in range(i+1,min(len(s),i+r)))
  for n in range(r,5):
   result=None;cnt=0
   for L in range(0,8):
    for s in it.product(range(n),repeat=L):
     if not sparse(s) or contains(s,u):continue
     cnt+=1
     if all(not sparse(s[:j]+(a,)+s[j:]) or contains(s[:j]+(a,)+s[j:],u) for j in range(L+1) for a in range(n)):result=s;break
    if result is not None:break
   out.append({'pattern':u,'alphabet':n,'length_cap':7,'free_sparse_words':cnt,'minimum_witness_through_cap':result});emit(363046,{'scope':'four fixed forbidden patterns aba,abc,abca,abcabc; alphabet sizes r..4; all words through length7 until minimum saturated witness; subsequence equality pattern up to injective renaming; r-sparse windows. Finite values do not settle asymptotic dichotomy.','cases':out})
