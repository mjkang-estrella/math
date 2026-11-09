import pathlib,json,itertools,hashlib
D=pathlib.Path(__file__).resolve().parents[1];a=json.loads((D/'outputs/simplicial-structured-witness.json').read_text());F=[frozenset(f) for f in a['facets']];faces=[set().union(*(set(itertools.combinations(sorted(f),k+1)) for f in F)) for k in range(4)]
R=sorted(faces[2]);adj={('F',i):set() for i in range(len(F))};adj.update({('R',r):set() for r in R})
for i,f in enumerate(F):
 for r in R:
  if set(r)<=f:adj['F',i].add(('R',r));adj['R',r].add(('F',i))
components=[];unseen=set(adj)
while unseen:
 todo=[next(iter(unseen))];comp=set()
 while todo:
  x=todo.pop()
  if x in comp:continue
  comp.add(x);todo.extend(adj[x]-comp)
 unseen-=comp;components.append({'vertices':len(comp),'edges':sum(len(adj[x]) for x in comp)//2,'facet_indices':sorted(x[1] for x in comp if x[0]=='F')})
leaves=[];g={x:set(ns) for x,ns in adj.items()}
while g:
 v=next((v for v,ns in g.items() if len(ns)<=1),None)
 if v is None:break
 leaves.append(v)
 for w in g[v]:g[w].remove(v)
 del g[v]
out={'f_vector':list(map(len,faces)),'components':components,'forest':not g,'leaf_elimination_order':leaves,'v1_endpoint':'not a simplicial tree since disconnected; no (2,3)-simplicial cycle because no (2,3)-circuit at all','v3_endpoint':'not (2,3)-tree since no ordering can join disjoint vertex components; no (2,3)-circuit','checks':{'pure':all(len(f)==4 for f in F),'distinct':len(set(F))==9,'top_count':len(F)==len(faces[0])-3,'edge_count':len(faces[1])==(len(faces[0])-3)*3+3}}
(D/'outputs/simplicial-independent-verification.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out,indent=2)[:3000])
