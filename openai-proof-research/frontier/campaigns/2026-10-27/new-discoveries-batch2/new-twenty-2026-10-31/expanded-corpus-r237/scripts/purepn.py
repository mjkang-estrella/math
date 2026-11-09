from pathlib import Path
import itertools,collections,json,time
L=Path(__file__).resolve().parents[1]
def make(v,E):
 a=[set() for _ in range(v)]
 for x,y in E:a[x].add(y);a[y].add(x)
 return a
def iso(a,b):
 if len(a)!=len(b):return False
 ds=sorted(map(len,a))
 if ds!=sorted(map(len,b)):return False
 groups=[[i for i in range(len(a)) if len(a[i])==d] for d in set(ds)]
 targets=[[i for i in range(len(b)) if len(b[i])==len(a[g[0]])] for g in groups]
 for parts in itertools.product(*(itertools.permutations(g) for g in targets)):
  p=dict(zip(itertools.chain.from_iterable(groups),itertools.chain.from_iterable(parts)))
  if all({p[j] for j in a[i]}==b[p[i]] for i in range(len(a))):return True
 return False
def step(a,n):
 E=[(i,j) for i in range(len(a)) for j in a[i] if i<j];I={frozenset(e):i for i,e in enumerate(E)};H=make(len(E),[])
 def dfs(path):
  if len(path)==n:
   es=[I[frozenset(e)] for e in zip(path,path[1:])]
   for u,v in zip(es,es[1:]):H[u].add(v);H[v].add(u)
   return
  for w in a[path[-1]]:
   if w not in path:dfs(path+[w])
 for v in range(len(a)):dfs([v])
 return H
def conv(a,n):
 sizes=[]
 for t in range(10):
  e=sum(map(len,a))//2;sizes.append([len(a),e])
  if not e:return 'terminate',sizes
  if len(a)>15 or e>22:return 'size_cap',sizes
  b=step(a,n)
  if iso(a,b):return 'converge',sizes
  a=b
 return 'iteration_cap',sizes
C=collections.Counter();H=[]
for v in range(3,7):
 E=list(itertools.combinations(range(v),2))
 for mask in range(1<<len(E)):
  edges=[e for i,e in enumerate(E) if mask>>i&1]
  if len(edges)>v+2:continue
  a=make(v,edges);seen={0};todo=[0]
  while todo:
   for w in a[todo.pop()]:
    if w not in seen:seen.add(w);todo.append(w)
  if len(seen)!=v:continue
  for n in range(4,v+1):
   status,sizes=conv(a,n);C[f'{v},{n},{status}']+=1
   if status=='converge' and len(edges)!=v:
    minimal=True
    for e in edges:
     if conv(make(v,[f for f in edges if f!=e]),n)[0]=='converge':minimal=False;break
    if minimal:H.append({'v':v,'edges':edges,'n':n,'sizes':sizes});print('HIT',H[-1],flush=True)
 print('completed v',v,dict(C),flush=True)
 (L/'outputs/purepn.json').write_text(json.dumps({'coverage':dict(C),'minimality_screen_hits':H},indent=2))
