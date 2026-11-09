import pathlib,json,itertools,resource,os
resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3));os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);import networkx as nx
D=pathlib.Path(__file__).resolve().parents[1];out=[]
for index,G in enumerate(nx.graph_atlas_g()):
 n=len(G)
 if n<3 or max(dict(G.degree()).values())!=3 or not nx.is_biconnected(G):continue
 es=list(G.edges());E=set(range(len(es)));cycles=[set()];double=[set()]
 for mask in range(1,1<<len(es)):
  selected={j for j in E if mask>>j&1};H=nx.from_edgelist(es[j] for j in selected)
  if all(d==2 for _,d in H.degree()) and all(len(c)%2==0 for c in nx.connected_components(H)):cycles.append(selected)
  if all(len(c)==6 and sorted(H.degree(v) for v in c)==[1,1,1,1,3,3] and nx.is_tree(H.subgraph(c)) for c in nx.connected_components(H)):
   leaves=[v for v,d in H.degree() if d==1]
   if not any(G.has_edge(a,b) for a,b in itertools.combinations(leaves,2)):double.append(selected)
 found=None
 for C in cycles:
  for S in double:
   if C&S:continue
   rest=E-C-S;verts=[v for j in rest for v in es[j]]
   if len(set(verts))==len(verts):found={'matching':sorted(rest),'cycles':sorted(C),'double_stars':sorted(S)};break
  if found is not None:break
 row={'id':381027,'atlas_index':index,'n':n,'regular':len(set(dict(G.degree()).values()))==1,'edges':es,'MED':found};out.append(row);print(json.dumps(row),flush=True);(D/'outputs/med-search.json').write_text(json.dumps(out,indent=2))
