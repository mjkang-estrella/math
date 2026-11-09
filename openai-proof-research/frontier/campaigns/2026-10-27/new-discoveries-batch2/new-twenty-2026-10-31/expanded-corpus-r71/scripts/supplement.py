import itertools as it,math,json,pathlib,networkx as nx
D=pathlib.Path(__file__).resolve().parents[1];O={}
G=nx.Graph();vs=list(it.combinations(range(7),3));G.add_nodes_from(vs);G.add_edges_from((a,b) for a,b in it.combinations(vs,2) if not set(a)&set(b));L=nx.line_graph(G)
O['375755']={'domain':'Reproduction of published KG(7,3) witness only','order':len(G),'edges':G.number_of_edges(),'Delta':max(dict(G.degree()).values()),'line_graph_diameter':nx.diameter(L),'claimed_h3_upper':4**3-4**2+4+2,'known_counterexample':True}
O['375932']={'domain':'All products P2 box Pn, n=2..25, explicit Hamilton cycle independently checked','tested':24,'violations':[]}
for n in range(2,26):
 H=nx.cartesian_product(nx.path_graph(2),nx.path_graph(n));cycle=[(0,j) for j in range(n)]+[(1,j) for j in range(n-1,-1,-1)];assert len(set(cycle))==len(H) and all(H.has_edge(a,b) for a,b in zip(cycle,cycle[1:]+cycle[:1]))
rows=[]
for q in [2,3]:
 pts=list(it.product(range(q+1),repeat=2))
 for n in range(3,6):
  best=-1;count=0
  for s in it.combinations(pts,n):
   least=min(abs((b[0]-a[0])*(c[1]-a[1])-(c[0]-a[0])*(b[1]-a[1])) for a,b,c in it.combinations(s,3));best=max(best,least);count+=1
  rows.append({'grid_denominator':q,'n':n,'subsets':count,'largest_minimum_doubled_area_numerator':best,'area_denominator':2*q*q})
O['376188']={'domain':'Every n-subset n=3..5 of rational square grids denominator 2 and3; finite diagnostic cannot address absolute exponent improvement','rows':rows}
(D/'outputs/supplement.json').write_text(json.dumps(O,indent=2)+'\n');print(json.dumps(O,indent=2))
