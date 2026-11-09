import sys;sys.path.insert(0,'/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/fresh-corpus-r10/pydeps')
import networkx as nx,itertools,json,pathlib
L=pathlib.Path(__file__).resolve().parents[1];out=[]
def lines(n):return sorted({tuple(sorted((a,b,a^b))) for a in range(1,1<<n) for b in range(a+1,1<<n)})
def sigma(ls,F):
 deg={}
 for i in F:
  for v in ls[i]:deg[v]=deg.get(v,0)+1
 return min(sum(deg.get(v,0) for v in l) for i,l in enumerate(ls) if i not in F)
ls=lines(4);G=nx.Graph();G.add_nodes_from(range(len(ls)))
for i,j in itertools.combinations(range(len(ls)),2):
 if set(ls[i])&set(ls[j]):G.add_edge(i,j)
cliques=list(nx.find_cliques(G));vals=[sigma(ls,set(c)) for c in cliques];out.append(dict(q=2,n=4,k=2,s=2,lines=len(ls),maximal_intersecting_families=len(cliques),sigma_values=vals,threshold=3,violations=sum(v>3 for v in vals),scope='all maximal intersecting families; monotonicity of sigma under adding members covers all proper subfamilies'))
ls=lines(6)
for mask in [3,31]:
 W=set(range(1,mask+1))
 # mask3 denotes fixed 2space; mask31 fixed5space
 F={i for i,l in enumerate(ls) if (bool(set(l)&W) if mask==3 else set(l)<=W)}
 out.append(dict(q=2,n=6,k=2,s=3,construction='meets fixed 2space' if mask==3 else 'contained in fixed 5space',members=len(F),sigma=sigma(ls,F),threshold=15,violation=sigma(ls,F)>15))
(L/'outputs/geometry.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
