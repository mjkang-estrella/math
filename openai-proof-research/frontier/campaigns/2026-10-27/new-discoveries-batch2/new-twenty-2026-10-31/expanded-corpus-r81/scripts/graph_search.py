import networkx as nx,numpy as np,itertools as it,json,collections
from pathlib import Path
D=Path(__file__).resolve().parents[1];out={str(i):{'tested':0,'violations':[]} for i in [315992,335372,345836,347417,349737,350595,367516,369902,376422,382229]}
def record(i,bad,g,extra=None):
 r=out[str(i)];r['tested']+=1
 if bad:r['violations'].append({'graph6':nx.to_graph6_bytes(g,header=False).decode().strip(),'extra':extra})
def cycles(g):
 n=len(g); ans=[]
 for s in range(n):
  def dfs(path):
   for v in g[path[-1]]:
    if v==s and len(path)>2 and path[1]<path[-1]:ans.append(tuple(path))
    elif v>s and v not in path:dfs(path+[v])
  dfs([s])
 return ans
def matchings(g):
 def rec(vs):
  if not vs:return [set()]
  v=min(vs);return [{tuple(sorted((v,w)))}|m for w in g[v] if w in vs for m in rec(vs-{v,w})]
 return rec(set(g))
for g in nx.graph_atlas_g():
 n=len(g)
 if not n:continue
 a=nx.to_numpy_array(g);de=np.array([g.degree(v) for v in g]);m=g.number_of_edges();ev=np.linalg.eigvalsh(np.diag(de)-a)[::-1]
 record(315992,any(np.cumsum(ev)>[m+t*(t+1)/2+1e-8 for t in range(1,n+1)]),g)
 energy=float(abs(np.linalg.eigvalsh(a)).sum());le=float(abs(ev-2*m/n).sum());record(345836,energy>le+1e-8,g,[energy,le])
 if nx.graph_clique_number(g) if hasattr(nx,'graph_clique_number') else False:pass
 if not any(len(c)>=4 for c in nx.find_cliques(g)):
  best=min(g.subgraph(s).number_of_edges() for s in it.combinations(g,n//2));record(347417,18*best>n*n,g,best)
 if nx.check_planarity(g)[0]:
  best=max(len(s) for k in range(n+1) for s in it.combinations(g,k) if all(d<=1 for v,d in g.subgraph(s).degree()))
  record(350595,3*(n-best)>2*n,g,n-best)
 cs=cycles(g)
 if not nx.is_bipartite(g) and 4*m>n*n-4*n+19:
  ls={len(c) for c in cs};record(369902,bool(ls and ls!=set(range(min(ls),max(ls)+1))),g,sorted(ls))
 if n>=2 and nx.is_connected(g):
  dist=np.array([[nx.shortest_path_length(g,i,j) for j in g] for i in g]);tr=dist.sum(axis=1);norm=np.eye(n)-dist/np.sqrt(tr[:,None]*tr[None,:]);gap=np.linalg.eigvalsh(norm)[1];record(367516,gap<2/3-1e-8,g,float(gap))
 if all(d==3 for d in de) and nx.is_connected(g) and not list(nx.bridges(g)):
  ms=matchings(g);edges=list(g.edges());target=tuple([2]*len(edges));vec=[tuple(int(e in mm or e[::-1] in mm) for e in edges) for mm in ms];ok=any(all(sum(v[j] for v in vv)==2 for j in range(len(edges))) for vv in it.combinations_with_replacement(vec,6));record(376422,not ok,g)
 if all(d==4 for d in de):
  ok=False
  for mask in range(1,1<<n):
   vs={v for v in g if mask>>v&1};h=g.subgraph(vs)
   if any(d<3 for _,d in h.degree()):continue
   remove=[v for v,d in h.degree() if d==4]
   if len(remove)%2==0 and len(nx.max_weight_matching(h.subgraph(remove),maxcardinality=True))*2==len(remove):ok=True;break
  record(382229,not ok,g)
 if all(d==4 for d in de) and cs:
  girth=min(map(len,cs));short=[c for c in cs if len(c)==girth]
  counts=collections.Counter(tuple(sorted((c[j],c[(j+1)%girth]))) for c in short for j in range(girth))
  sigs={tuple(sorted((counts[tuple(sorted(e))] for e in g.edges(v)),reverse=True)) for v in g}
  if sigs in [{(3,2,2,1)},{(4,4,4,3)}]:record(349737,False,g,{'signature':list(sigs)[0],'note':'signature match; coloring not yet checked'})
(D/'outputs/graph-search.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
