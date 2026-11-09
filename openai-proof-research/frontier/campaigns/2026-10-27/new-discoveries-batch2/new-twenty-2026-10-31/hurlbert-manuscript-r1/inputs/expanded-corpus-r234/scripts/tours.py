import itertools,json,random,sys

def red(p):return tuple(sorted(p).index(x) for x in p)
def setup(n):
 ps=list(itertools.permutations(range(n))); es=[(red(p[:-1]),red(p[1:])) for p in ps];out={}
 for i,(a,b) in enumerate(es):out.setdefault(a,[]).append(i)
 return ps,es,out

def check(n,ps,tour):
 N=len(tour);adj=[set() for _ in range(N)]
 for i,e in enumerate(tour):
  p=ps[e]
  for a in range(n):
   for b in range(n):
    if p[a]<p[b]:adj[(i+a)%N].add((i+b)%N)
 deg=[0]*N
 for row in adj:
  for j in row:deg[j]+=1
 stack=[i for i,x in enumerate(deg) if not x];count=0
 while stack:
  i=stack.pop();count+=1
  for j in adj[i]:
   deg[j]-=1
   if not deg[j]:stack.append(j)
 return count==N

def exhaustive3():
 n=3;ps,es,out=setup(n);start=0;ans=[0,0]
 def rec(t,used,v):
  if len(t)==len(ps):
   if v!=es[start][0]:return
   good=check(n,ps,t);ans[not good]+=1
   if not good:print('FAIL',n,t,flush=True)
   return
  for e in out[v]:
   if not used>>e&1:rec(t+[e],used|1<<e,es[e][1])
 rec([start],1,es[start][1]);print('exhaustive n3 fixed first 123',ans,flush=True)

def randoms(n,trials):
 ps,es,out=setup(n);rng=random.Random(356266+n);bad=0
 for z in range(trials):
  avail={v:rng.sample(x,len(x)) for v,x in out.items()};stack=[(es[0][0],None)];tour=[]
  while stack:
   v,e=stack[-1]
   if avail[v]:
    k=avail[v].pop();stack.append((es[k][1],k))
   else:
    stack.pop()
    if e is not None:tour.append(e)
  tour.reverse()
  if not check(n,ps,tour):print('FAIL',n,z,tour,flush=True);bad+=1;break
 print('random n',n,'trials_completed',z+1,'bad',bad,flush=True)
exhaustive3()
for n,t in [(4,30000),(5,5000),(6,500)]:randoms(n,t)
