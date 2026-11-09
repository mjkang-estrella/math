from pathlib import Path
import networkx as nx,itertools as it,json
D=Path(__file__).resolve().parents[1];out={};rows=[]
for p in [3,5]:
 perms=set()
 for a,b,c,d in it.product(range(p),repeat=4):
  if (a*d-b*c)%p==0:continue
  images=[]
  for x in range(p+1):
   num,den=(a,c) if x==p else ((a*x+b)%p,(c*x+d)%p)
   images.append(p if den==0 else num*pow(den,-1,p)%p)
  perms.add(tuple(images))
 perms=sorted(perms);pairs=list(it.combinations(range(p+1),2));acts=[tuple(tuple(sorted((g[x],g[y]))) for x,y in pairs) for g in perms];g=nx.Graph();g.add_nodes_from(range(len(perms)))
 for i,j in it.combinations(range(len(perms)),2):
  if any(x==y for x,y in zip(acts[i],acts[j])):g.add_edge(i,j)
 # Vertex transitivity: translate any clique to contain identity; restrict to its neighbors.
 ident=perms.index(tuple(range(p+1)));cl=1+max(map(len,nx.find_cliques(g.subgraph(list(g[ident])))),default=0)
 rows.append({'q':p,'group_size':len(perms),'maximum_intersecting_size':cl,'point_stabilizer_size':len(perms)//len(pairs),'density':cl/(len(perms)//len(pairs))})
out['354580']={'space':'All invertible 2x2 matrices modulo scalar, prime q=3,5; exact maximum clique after translation to identity','rows':rows}
rows=[]
for n in range(3,13):
 tested=0;connected=0;bad=[];orbits=[{x,(-x)%n} for x in range(1,n//2+1)]
 for bits in range(1<<len(orbits)):
  s=set().union(*(orbits[j] for j in range(len(orbits)) if bits>>j&1));g=nx.Graph();g.add_nodes_from(range(n));g.add_edges_from((x,(x+y)%n) for x in range(n) for y in s);tested+=1
  if not nx.is_connected(g):continue
  connected+=1;dp={(1,0)}
  for _ in range(1,n):dp={(mask|(1<<v),v) for mask,u in dp for v in g[u] if not mask>>v&1}
  if not any(g.has_edge(u,0) for mask,u in dp):bad.append(bits)
 rows.append({'n':n,'all_inverse_closed_connection_sets':tested,'connected':connected,'nonhamiltonian':bad})
out['357692']={'space':'Cyclic groups Z_n n=3..12, all inverse-closed connection sets excluding identity','rows':rows,'note':'Avoids degenerate order endpoints; cyclic subfamily only'}
(D/'outputs/group-search.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2))
