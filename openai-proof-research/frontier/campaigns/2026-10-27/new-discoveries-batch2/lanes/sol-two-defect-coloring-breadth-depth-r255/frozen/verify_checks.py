import pathlib,json,itertools,collections
L=pathlib.Path(__file__).parent
r=next(x for x in json.loads((L/'repair-results.json').read_text()) if x['name']=='K33');es=r['edges'];c=tuple(r['one_step_fail']['colors']);n=6
inc=[[i for i,e in enumerate(es) if v in e] for v in range(n)]
def defect(c):
 assert all(len({c[i] for i in t})==3 for t in inc)
 s=[{c[i] for i in t} for t in inc]
 return sum(len(s[a]|s[b])==4 for a,b in es)
def nexts(c):
 for a,b in itertools.combinations(range(5),2):
  adj={v:set() for v in range(n)}
  for i,(u,v) in enumerate(es):
   if c[i] in (a,b):adj[u].add(v);adj[v].add(u)
  remaining={v for v in range(n) if adj[v]}
  while remaining:
   todo=[remaining.pop()];verts=set(todo)
   while todo:
    v=todo.pop()
    for w in adj[v]:
     if w not in verts:verts.add(w);remaining.discard(w);todo.append(w)
   yield tuple(a+b-x if x in (a,b) and u in verts else x for x,(u,v) in zip(c,es))
assert defect(c)==2
layers=[{c}];seen={c};parents={}
for t in range(3):
 layer=set()
 for x in layers[-1]:
  for y in nexts(x):
   if y not in seen:seen.add(y);layer.add(y);parents[y]=x
 layers.append(layer)
assert all(defect(x)>0 for layer in layers[:3] for x in layer)
end=next(x for x in layers[3] if defect(x)==0);path=[end]
while path[-1]!=c:path.append(parents[path[-1]])
path.reverse()
out={'verified':True,'scope':'this K33 coloring has minimum Kempe distance exactly 3 to normal colorings','layer_sizes':[len(x) for x in layers],'path':path,'path_defects':[defect(x) for x in path]}
(L/'check-receipt.json').write_text(json.dumps(out,indent=2));print(json.dumps(out))
