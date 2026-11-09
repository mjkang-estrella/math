import pathlib,json,math,csv
D=pathlib.Path(__file__).resolve().parents[1]
rows=json.loads((D/'outputs/totient-lazy.json').read_text())
def factors(n):
 f=[];p=2
 while p*p<=n:
  e=0
  while n%p==0:n//=p;e+=1
  if e:f.append([p,e])
  p+=1
 if n>1:f.append([n,1])
 return f
def phi(n):
 z=n
 for p,e in factors(n):z=z//p*(p-1)
 return z
def canon(a,v,p=-1):return '('+''.join(sorted(canon(a,u,v) for u in a[v] if u!=p))+')'
out=[]
for row in rows:
 tree={int(a):b for a,b in row['embedding'].items()};parents={}
 for v,ws in tree.items():
  for w in ws:
   assert w not in parents and phi(w)==v and w in tree
   parents[w]=v
 assert len(parents)==len(tree)-1 and set(tree)-set(parents)=={1}
 # independently root at graph centre, check equal 3 arms and regular depth/edge subdivision.
 a={v:set(ws) for v,ws in tree.items()}
 for w,v in parents.items():a[w].add(v)
 distances={}
 for v in a:
  dist={v:0};todo=[v]
  for x in todo:
   for y in a[x]:
    if y not in dist:dist[y]=dist[x]+1;todo.append(y)
  distances[v]=dist
 centres=[v for v in a if max(distances[v].values())==min(max(d.values()) for d in distances.values())]
 assert len(centres)==1
 centre=centres[0];layers={}
 for v,d in distances[centre].items():layers.setdefault(d,[]).append(v)
 k=row['stage'];assert len(tree)==6*2**k-8 and len(a[centre])==3
 for d,vs in layers.items():
  if d==0:continue
  expected=1 if d==3*(k-1)+1 else (3 if d%3==0 else 2)
  assert all(len(a[v])==expected for v in vs)
 leaves=[v for v,ws in tree.items() if not ws]
 # 1 is not needed in A: it is in every leaf orbit.
 A=[v for v in leaves if v!=1];closure=set()
 for v in A:
  while v not in closure:closure.add(v);v=phi(v)
 assert closure==set(tree)
 cert=[{'n':v,'factorization':factors(v),'phi':phi(v),'parent':parents.get(v)} for v in sorted(tree)]
 (D/f'outputs/totient-stage{k}-certificate.json').write_text(json.dumps({'A':A,'vertices':cert,'children':row['embedding'],'centre':centre,'layer_sizes':{d:len(v) for d,v in layers.items()}},indent=2))
 out.append({'stage':k,'order':len(tree),'edges':len(parents),'centre':centre,'A_size':len(A),'max_label':max(tree),'layers':{d:len(v) for d,v in layers.items()},'all_arithmetic_and_closure_checks':True})
print(json.dumps(out,indent=2));(D/'outputs/totient-independent.json').write_text(json.dumps(out,indent=2))
