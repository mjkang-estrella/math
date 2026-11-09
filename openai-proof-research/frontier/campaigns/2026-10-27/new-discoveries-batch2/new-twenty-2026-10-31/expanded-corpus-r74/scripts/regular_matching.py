import pathlib,itertools,json,os,resource,time
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
import networkx as nx
D=pathlib.Path(__file__).resolve().parents[1]
# Reuse only the exact solver definitions, not the atlas main loop.
s=(D/'scripts/graph_search.py').read_text();exec(s[s.index('def colorable'):s.index('counts={')])
rows=[]
def test(G,name):
 n=len(G);deg=max(dict(G.degree()).values());es,ms=matchings(G);size=max(map(len,ms));maxima=[set(m) for m in ms if len(m)==size];r=0
 while True:
  good=[set(rem) for rem in itertools.combinations(range(len(es)),r) if colorable([e for j,e in enumerate(es) if j not in rem],deg,n)]
  if good:break
  r+=1
 bad=[sorted(m) for m in maxima if not any(rem<=m for rem in good)];res={'name':name,'n':n,'edges':es,'degree':deg,'maximum_matching_size':size,'maximum_matchings':len(maxima),'resistance':r,'optimal_deletions':len(good),'bad_maximum_matchings':bad};rows.append(res);print(json.dumps(res),flush=True);(D/'outputs/regular-matching.json').write_text(json.dumps(rows,indent=2))
# Two once-subdivided complete graphs joined at their new vertices: cubic with a bridge.
H=nx.complete_graph(4);H.remove_edge(0,1);H.add_edges_from([(0,4),(1,4)]);G=nx.disjoint_union(H,H);G.add_edge(4,9);test(G,'two subdivided K4 blocks with bridge')
# Petersen; small generalized Petersen graphs and cubic prisms.
for n in range(3,9):
 for k in range(1,(n-1)//2+1):
  G=nx.Graph();G.add_nodes_from(range(2*n));G.add_edges_from((i,(i+1)%n) for i in range(n));G.add_edges_from((i,i+n) for i in range(n));G.add_edges_from((i+n,((i+k)%n)+n) for i in range(n))
  if colorable(list(G.edges()),3,len(G)):continue
  test(G,f'GP({n},{k})')
