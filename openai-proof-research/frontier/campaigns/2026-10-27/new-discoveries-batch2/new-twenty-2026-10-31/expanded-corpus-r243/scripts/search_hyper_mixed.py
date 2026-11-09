import itertools,random,time,json,sys
rng=random.Random(243);start=time.monotonic()
def test(n,es):
 full=(1<<n)-1;adj=[1<<i for i in range(n)];inc=[[] for i in range(n)]
 for e in es:
  for v in range(n):
   if e>>v&1:adj[v]|=e;inc[v].append(e)
 seen=1
 while True:
  z=seen
  for v in range(n):
   if seen>>v&1:seen|=adj[v]
  if seen==z:break
 if seen!=full:return None
 def close(s):
  obs=0
  for v in range(n):
   if s>>v&1:obs|=adj[v]
  while True:
   old=obs
   for v in range(n):
    if obs>>v&1:
     missing=adj[v]&~obs
     if missing and any(missing&~e==0 for e in inc[v]):obs|=missing
   if old==obs:return obs
 for ss in itertools.combinations(range(n),n//4):
  if close(sum(1<<v for v in ss))==full:return True
 return False
mode=sys.argv[1];counter=0;connected=0
for n in ([4,5] if mode=='exhaust' else range(7,21)):
 edges=[sum(1<<v for v in e) for r in range(3,min(n,6)+1) for e in itertools.combinations(range(n),r)];total=(1<<len(edges)) if mode=='exhaust' else 20000
 for z in range(total):
  if mode=='exhaust':es=[e for i,e in enumerate(edges) if z>>i&1]
  else:
   p=rng.choice([.025,.05,.08,.12,.2,.35,.6]);es=[e for e in edges if rng.random()<p]
  r=test(n,es);counter+=1;connected+=r is not None
  if r is False:print(json.dumps({'counterexample':{'n':n,'edges':es},'tested':counter}),flush=True);sys.exit(2)
 print(json.dumps({'n':n,'tested':total,'connected_cumulative':connected,'counterexamples':0,'elapsed':time.monotonic()-start}),flush=True)
