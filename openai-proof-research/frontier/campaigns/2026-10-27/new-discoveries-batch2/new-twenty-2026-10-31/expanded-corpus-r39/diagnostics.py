import os,resource,time,json,math,itertools,random
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_AS,(2*1024**3,2*1024**3));resource.setrlimit(resource.RLIMIT_CPU,(150,150))
# KKT: canonical binomial shadow; only evaluate source-defined domain m<=choose(n,r).
def shadow(m,r):
 s=0;upper=10**6
 for j in range(r,0,-1):
  if not m:break
  a=j
  while math.comb(a+1,j)<=m:a+=1
  s+=math.comb(a,j-1);m-=math.comb(a,j)
 return s
for n in range(4,15,2):
 r=n//2;N=math.comb(n,r);v=[shadow(m,r)-m for m in range(N+1)];pref=[];z=0
 for x in v:z=min(z,x);pref.append(z)
 bad=[];mn=10**9;arg=None;tested=0
 for a in range(N+1):
  for k in range(a+1): # k+N-a <= N, otherwise undefined in Definition2.1
   gap=v[a]+pref[k+N-a]-v[N]-v[k];tested+=1
   if gap<mn:mn=gap;arg=[a,k]
   if gap<0:bad.append([a,k,gap])
 print(json.dumps({'route':'KK','n':n,'pairs':tested,'min_gap':mn,'argmin':arg,'counterexamples':bad[:10],'domain_limit':'Only inputs to kappa-star <= N'}),flush=True)
# Enclaveless game: selected vertices S legal iff every v in S has a neighbor outside S.
from functools import lru_cache
def game(n,edges):
 adj=[0]*n
 for i,j in edges:adj[i]|=1<<j;adj[j]|=1<<i
 full=(1<<n)-1
 @lru_cache(None)
 def go(s):
  vals=[]
  for v in range(n):
   if s>>v&1:continue
   t=s|1<<v;outside=full^t
   if all(not(t>>u&1) or adj[u]&outside for u in range(n)):vals.append(go(t))
  if not vals:return s.bit_count()
  return (min if s.bit_count()%2==0 else max)(vals)
 return go(0)
random.seed(3901)
for n in range(4,15):
 vals=[]
 for a in range(2,n-1):
  es=[(i,j) for i in range(a) for j in range(a,n)];v=game(n,es);vals.append(['complete-bipartite',a,n-a,v])
 for t in range(50):
  es=[(i,j) for i in range(n) for j in range(i+1,n) if random.random()<random.choice([.25,.4,.6])];deg=[0]*n
  for i,j in es:deg[i]+=1;deg[j]+=1
  if min(deg)<2:continue
  v=game(n,es);vals.append(['random',t,v])
  if 2*v<n:print(json.dumps({'route':'game','counterexample':es,'n':n,'value':v}),flush=True);raise SystemExit
 print(json.dumps({'route':'game','n':n,'tested':len(vals),'min_value':min(x[-1] for x in vals),'structured':vals[:n-3]}),flush=True)
