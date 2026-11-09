import os,resource,collections,itertools,json,heapq,time
os.sched_setaffinity(0,sorted(os.sched_getaffinity(0))[:2]);resource.setrlimit(resource.RLIMIT_CPU,(120,120));resource.setrlimit(resource.RLIMIT_AS,(6*1024**3,6*1024**3))
from pathlib import Path
o=Path(__file__).resolve().parent
# Exhaustive BFS certificate diagnostics for C_12 categorical K_4.
V=list(itertools.product(range(12),range(4)));adj={v:{w for w in V if (w[0]-v[0])%12 in (1,11) and w[1]!=v[1]} for v in V}
def bfs(v,deleted=None):
 d={v:0};q=collections.deque([v])
 while q:
  u=q.popleft()
  for w in adj[u]-{deleted}:
   if w not in d:d[w]=d[u]+1;q.append(w)
 return d
D={v:bfs(v) for v in V};redundant=all(all(d[w]==D[v][w] for w in d) and len(d)==47 for x in V for v in V if v!=x for d in [bfs(v,x)])
surrounded=[(u,v) for u in V for v in V if u!=v and adj[u]<=adj[v]|{v}]
print('GRAPH',json.dumps(dict(vertices=48,edges=sum(map(len,adj.values()))//2,diameter=max(max(d.values()) for d in D.values()),all_redundant=redundant,surrounded=surrounded)),flush=True)
# Exact row transfer maximum packing. States (previous occupied, vertical pending).
def transitions(width,q,p,last):
 ans={}
 def rec(i,t,s,count):
  if i>=width:
   ans[t,s]=max(ans.get((t,s),-1),count);return
  if p>>i&1:rec(i+1,t,s,count);return
  rec(i+1,t,s,count)
  if (q|p|(p<<1)|(p>>1)|t|(t<<1))>>i&1:return
  if not last:rec(i+1,t|1<<i,s|1<<i,count+1)
  if i+1<width and not ((q|p|(p<<1)|(p>>1))>>(i+1)&1):rec(i+2,t|3<<i,s,count+1)
 rec(0,p,0,0);return ans
from functools import lru_cache
T=lru_cache(None)(transitions)
for w in [1,3,5,7]:
 dp={(0,0):0}
 for h in range(1,31):
  nd={}
  for (q,p),v in dp.items():
   for state,c in T(w,q,p,False).items():nd[state]=max(nd.get(state,-1),v+c)
  dp=nd
  best=max(v for (q,p),v in dp.items() if p==0)
  if h%4==2:print('DOMINO',h,w,best,'target', (h*w+2)//4,'match',4*best==h*w+2,flush=True)
# Ordered multiset permutations with one extra digit; bounded 10000 tested candidates/base.
import sympy
def permutations(counts,prefix=()):
 if not any(counts):yield prefix;return
 for a in range(len(counts)):
  if counts[a] and (prefix or a):
   counts[a]-=1;yield from permutations(counts,prefix+(a,));counts[a]+=1
for b in range(4,21):
 for zero in [True,False]:
  gens=[]
  for extra in range(b) if zero else range(1,b):
   c=[1]*b;c[0]=int(zero);c[extra]+=1;gens.append(permutations(c))
  found=None
  for steps,d in enumerate(heapq.merge(*gens),1):
   n=0
   for a in d:n=n*b+a
   if sympy.isprime(n):found=dict(n=n,digits=d,sum=sum(d),expected=b*(b-1)//2+(2 if b%4==3 else 1));break
   if steps>=10000:break
  print('PRIME',b,zero,steps,json.dumps(found),flush=True)
