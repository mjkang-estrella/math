import sys,random,collections,json
k,q=map(int,sys.argv[1:]);keys=[(1,),(1,1),(1,2),(2,1)]
for i in range(2,k):keys += [(i,i),(i,i,'p'),(i,i+1),(i+1,i)]
keys=keys[:k];index={a:i for i,a in enumerate(keys)}
def neighbors(v):
 side,coords=v;X=dict(zip(keys,coords))
 for c in range(q):
  Y={(1,):c};a1=X[(1,)] if side==0 else c;b1=c if side==0 else X[(1,)]
  for key in keys[1:]:
   if key==(1,1):z=a1+b1-X[key]-a1*b1
   else:
    if key==(1,2):prev=(1,1);orient=0
    elif key==(2,1):prev=(1,1);orient=1
    elif len(key)==3:prev=(key[0],key[0]-1);orient=0
    elif key[0]==key[1]:prev=(key[0]-1,key[0]);orient=1
    elif key[1]>key[0]:prev=(key[0],key[0]);orient=0
    else:prev=(key[1],key[1],'p');orient=1
    a=X[prev] if side==0 else Y[prev];b=Y[prev] if side==0 else X[prev]
    z=-X[key]-a-b-(a1*b if orient==0 else a*b1)
   Y[key]=z%q
  yield (1-side,tuple(Y[key] for key in keys))
rng=random.Random(121);bound=k+4 if k%2==0 else k+5
roots=[(0,(0,)*k)]+[(rng.randrange(2),tuple(rng.randrange(q) for _ in range(k))) for _ in range(99)]
for ri,root in enumerate(roots):
 parent={root:None};depth={root:0};todo=collections.deque([root]);short=None
 while todo and short is None:
  v=todo.popleft()
  if 2*depth[v]+1>=bound:continue
  for w in neighbors(v):
   if w==parent[v]:continue
   if w not in parent:parent[w]=v;depth[w]=depth[v]+1;todo.append(w)
   elif depth[v]+depth[w]+1<bound:
    x,y=v,w;px=[x];py=[y]
    while depth[x]>depth[y]:x=parent[x];px.append(x)
    while depth[y]>depth[x]:y=parent[y];py.append(y)
    while x!=y:x=parent[x];y=parent[y];px.append(x);py.append(y)
    short=px+list(reversed(py[:-1]));break
 if short:
  print(json.dumps(dict(k=k,q=q,root_index=ri,cycle_length=len(short),cycle=short,claimed_bound=bound)),flush=True);break
 print(json.dumps(dict(k=k,q=q,root_index=ri,vertices_explored=len(parent),no_cycle_below=bound)),flush=True)
