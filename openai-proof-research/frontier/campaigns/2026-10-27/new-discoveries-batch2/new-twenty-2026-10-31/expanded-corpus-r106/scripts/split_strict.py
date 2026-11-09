import random,json
rng=random.Random(106371911)
def color(edges,n,d):
 masks=[0]*n;todo=set(range(len(edges)))
 def rec():
  if not todo:return True
  k=min(todo,key=lambda k: (d-((masks[edges[k][0]]|masks[edges[k][1]]).bit_count())))
  u,v=edges[k];avail=((1<<d)-1)&~(masks[u]|masks[v]);todo.remove(k)
  while avail:
   c=avail&-avail;avail-=c;masks[u]|=c;masks[v]|=c
   if rec():return True
   masks[u]^=c;masks[v]^=c
  todo.add(k);return False
 return rec()
out=[]
for n,d in [(6,3),(10,4),(12,5),(14,5)]:
 graphs=0;splits=0;checks=0
 for trial in range(20):
  E=set()
  for z in range(d):
   for attempt in range(10000):
    p=list(range(n));rng.shuffle(p);M={tuple(sorted(p[j:j+2])) for j in range(0,n,2)}
    if not E&M:E|=M;break
   else:raise RuntimeError('matching construction failed')
  # Keep connected inputs only
  seen={0}
  while True:
   new=seen|{v for u,v in E if u in seen}|{u for u,v in E if v in seen}
   if new==seen:break
   seen=new
  if len(seen)!=n:continue
  graphs+=1;nei=sorted(v if u==0 else u for u,v in E if u==0 or v==0)
  for b in range(1,1<<(d-1)):
   H=[(n if ((b>>nei.index(v))&1) else 0,v) if u==0 else (u,n if ((b>>nei.index(u))&1) else 0) if v==0 else (u,v) for u,v in E]+[(0,n)]
   splits+=1
   for k in range(len(H)):
    checks+=1
    if not color(H[:k]+H[k+1:],n+1,d):
     out.append({'counterexample_candidate':[n,d,sorted(E),b,k]});open('outputs/split-strict.json','w').write(json.dumps(out));print(out[-1],flush=True);raise SystemExit
  print('progress',n,trial,graphs,splits,checks,flush=True)
 out.append({'n':n,'delta':d,'connected_class1_graphs':graphs,'nonempty_splits_up_to_side_swap':splits,'edge_deletion_color_checks':checks,'failures':0});open('outputs/split-strict.json','w').write(json.dumps(out,indent=2))
