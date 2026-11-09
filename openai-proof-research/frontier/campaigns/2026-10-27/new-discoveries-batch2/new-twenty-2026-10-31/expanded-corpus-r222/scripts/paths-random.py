import pathlib
import itertools,json,sys,time
# All simple cubic supergraphs of the directed Hamilton path 0,...,N-1.
# Additional degree: endpoints 2, internal 1. No added consecutive edge.
def threeconn(N,E):
 adj=[[] for _ in range(N)]
 for u,v in E:adj[u].append(v);adj[v].append(u)
 # Undirected unit-capacity local max flows from 0 to every other vertex.
 for t in range(1,N):
  c={(u,v):1 for u in range(N) for v in adj[u]}
  for _ in range(3):
   p={0:-1};Q=[0]
   for u in Q:
    for v in adj[u]:
     if c[u,v] and v not in p:p[v]=u;Q.append(v)
    if t in p:break
   if t not in p:return False
   v=t
   while v: u=p[v];c[u,v]-=1;c[v,u]+=1;v=u
 return True

import random,json,sys
rng=random.Random(222)
for N in [20,24,30,40,60,80,100]:
 count=tries=over=qual=0;mx=0;f=[0,1]
 for _ in range(N):f.append(sum(f[-2:]))
 bound=f[N//2+2]+1
 for z in range(10000):
  d=[2]+[1]*(N-2)+[2];E=list(zip(range(N-1),range(1,N)));ok=True;tries+=1
  for i in range(N):
   opts=[j for j in range(i+2,N) if d[j]]
   if len(opts)<d[i]:ok=False;break
   # Structured short-jump bias in three quarters of trials; otherwise uniform.
   J=[]
   for _ in range(d[i]):
    if z%4:
     w=[1/(j-i)**(1+z%3) for j in opts];j=rng.choices(opts,w)[0]
    else:j=rng.choice(opts)
    opts.remove(j);J.append(j)
   for j in J:d[j]-=1;E.append((i,j))
   d[i]=0
  if not ok:continue
  count+=1;p=[0]*N;p[0]=1;a=[[] for _ in range(N)]
  for i,j in E:a[i].append(j)
  for i in range(N):
   for j in a[i]:p[j]+=p[i]
  mx=max(mx,p[-1]);over+=p[-1]>bound
  if p[-1]>bound and threeconn(N,E):
   qual+=1;print("WITNESS",N,p[-1],E,flush=True)
 print(json.dumps({'vertices':N,'attempts':tries,'completed':count,'bound':bound,'unfiltered_max_paths':mx,'overbound_checked':over,'three_edge_connected_violations':qual}),flush=True)
