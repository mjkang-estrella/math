import os;os.environ['OPENBLAS_NUM_THREADS']='1';os.environ['OMP_NUM_THREADS']='1'
import sys;sys.path.insert(0,'.deps')
import networkx as nx,itertools,json,time,signal
# Reuse exact color search without executing the exploratory driver.
s=open('diagnostics.py').read();ns={};exec(s[s.index('def color(G):'):s.index('records=[]')],dict(nx=nx,signal=signal),ns);color=ns['color']
I=nx.icosahedral_graph();v=0;emb=nx.check_planarity(I)[1];boundary=list(emb.neighbors_cw_order(v));P=I.copy();P.remove_node(v)
# certify the boundary is the hole rim
assert len(boundary)==5 and all(P.has_edge(boundary[i],boundary[(i+1)%5]) for i in range(5))
def relabel(G):return nx.convert_node_labels_to_integers(G)
r=[]
for copies in range(1,5):
 # Start one punctured icosahedron; fill each triangular face by another
 # punctured icosahedron with a triangular face removed (vertices retained).
 G=I.copy()
 for j in range(copies-1):
  e=nx.check_planarity(G)[1];a,b=next(iter(G.edges()));face=e.traverse_face(a,b);assert len(face)==3
  J=I.copy();ej=nx.check_planarity(J)[1];c,d=next(iter(J.edges()));fj=ej.traverse_face(c,d);mapping={fj[k]:face[k] for k in range(3)};n=max(G)+1
  for z in J:
   if z not in mapping:mapping[z]=n;n+=1
  G=nx.compose(G,nx.relabel_nodes(J,mapping))
 col,nodes=color(relabel(G));r.append(dict(family='icosahedra glued along triangle',copies=copies,n=len(G),nodes=nodes,coloring=col,edges=list(relabel(G).edges())))
# Glue two copies of punctured I along a 5-cycle in all dihedral orientations.
for reverse in [False,True]:
 for shift in range(5):
  G=P.copy();mapping={boundary[i]:boundary[(shift+(-i if reverse else i))%5] for i in range(5)};k=max(G)+1
  for z in P:
   if z not in mapping:mapping[z]=k;k+=1
  G=nx.compose(G,nx.relabel_nodes(P,mapping));G=relabel(G)
  assert nx.check_planarity(G)[0] and G.number_of_edges()==3*len(G)-6 and min(dict(G.degree()).values())>=4
  col,nodes=color(G);r.append(dict(family='two punctured icosahedra',reverse=reverse,shift=shift,n=len(G),nodes=nodes,coloring=col,edges=list(G.edges())))
# Source's patch alone: exact exhaustive rejection, distinction from closed triangulation.
col,nodes=color(relabel(P));r.append(dict(family='punctured icosahedron source-known control',n=len(P),nodes=nodes,coloring=col,edges=list(relabel(P).edges())))
for row in r:
 if row['coloring'] is not None:
  G=nx.Graph(row['edges']);c=row['coloring'];assert all({c[w] for w in G[v]}=={0,1,2} for v in G)
json.dump(r,open('structured-triangulations.json','w'),indent=2)
print([(x['family'],x['n'],x['coloring'] is not None,x['nodes']) for x in r])
