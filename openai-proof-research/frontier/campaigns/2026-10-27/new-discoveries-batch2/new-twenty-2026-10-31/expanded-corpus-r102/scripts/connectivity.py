import itertools,json,time

def connected(adj,keep):
 if not keep:return True
 seen={next(iter(keep))};todo=list(seen)
 while todo:
  a=todo.pop()
  for b in adj[a]&keep-seen:seen.add(b);todo.append(b)
 return seen==keep

def kc(adj,k,keep=None):
 if keep is None:keep=set(range(len(adj)))
 if len(keep)<=k:return False
 if any(len(adj[v]&keep)<k for v in keep):return False
 return all(connected(adj,keep-set(S)) for j in range(k) for S in itertools.combinations(keep,j))
def local(adj,s,t):
 # direct edge plus minimum vertex separator in G-st
 n=len(adj);direct=int(t in adj[s]);aa=[a.copy() for a in adj];aa[s].discard(t);aa[t].discard(s)
 rest=set(range(n))-{s,t}
 for j in range(n-1):
  for S in itertools.combinations(rest,j):
   keep=set(range(n))-set(S);seen={s};todo=[s]
   while todo:
    a=todo.pop()
    for b in (aa[a]&keep)-seen:seen.add(b);todo.append(b)
   if t not in seen:return j+direct
for n in range(4,7):
 start=time.monotonic();es=list(itertools.combinations(range(n),2));out={k:{'kconnected':0,'super':0,'uniform':0,'min_super_ratio':1,'min_uniform_ratio':1} for k in range(3,n)}
 for mask in range(1<<len(es)):
  adj=[set() for _ in range(n)];edges=[]
  for i,(a,b) in enumerate(es):
   if mask>>i&1:adj[a].add(b);adj[b].add(a);edges.append((a,b))
  for k,o in out.items():
   if not kc(adj,k):continue
   o['kconnected']+=1;ratio=sum(len(a)==k for a in adj)/n
   uniform=all(local(adj,a,b)==k for a,b in es)
   if uniform:o['uniform']+=1;o['min_uniform_ratio']=min(o['min_uniform_ratio'],ratio)
   super=True
   for a,b in edges:
    adj[a].remove(b);adj[b].remove(a);ok=kc(adj,k);adj[a].add(b);adj[b].add(a)
    if ok:super=False;break
   if super and any(kc(adj,k,set(range(n))-{v}) for v in range(n)):super=False
   if super:o['super']+=1;o['min_super_ratio']=min(o['min_super_ratio'],ratio)
 print(json.dumps({'n':n,'labelled_graphs':1<<len(es),'results':out,'seconds':time.monotonic()-start}),flush=True)
