import sys;sys.path.insert(0,'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/fresh-corpus-r10/pydeps')
import networkx as nx,itertools,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1];out=[]
for n in range(3,6):
 es=list(itertools.combinations(range(n),2));trees=[]
 for code in itertools.product(range(n),repeat=n-2):
  G=nx.from_prufer_sequence(code);trees.append(sum(1<<es.index(tuple(sorted(e))) for e in G.edges()))
 for t in range(1,n):
  H=nx.Graph();H.add_nodes_from(range(len(trees)))
  for i,j in itertools.combinations(range(len(trees)),2):
   if (trees[i]&trees[j]).bit_count()>=t:H.add_edge(i,j)
  clique,w=nx.max_weight_clique(H,weight=None);candidates=[]
  for j in range((n-1-t)//2+1):
   ell=t+2*j
   # balanced components, any forest of balanced sizes suffices for family cardinality by relabeling if sizes<=3 here
   comps=n-ell;a,b=divmod(n,comps);sizes=[a+1]*b+[a]*(comps-b);F=0;pos=0
   for size in sizes:
    for v in range(pos+1,pos+size):F|=1<<es.index((pos,v))
    pos+=size
   candidates.append(sum((T&F).bit_count()>=t+j for T in trees))
  r=dict(n=n,t=t,spanning_trees=len(trees),maximum=w,candidate_sizes=candidates,violation=w>max(candidates));out.append(r);print(json.dumps(r),flush=True);(L/'outputs/small-trees.json').write_text(json.dumps(out,indent=2))
