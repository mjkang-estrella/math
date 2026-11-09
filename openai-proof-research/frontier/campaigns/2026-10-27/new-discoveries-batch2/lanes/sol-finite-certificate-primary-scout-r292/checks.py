"""Run only through the fixed helper_guard.py. Exact combinatorial checks."""
import random,json,time,pathlib,itertools
L=pathlib.Path(__file__).resolve().parent
def strong(n,edges):
 for reverse in [False,True]:
  seen={0};todo=[0]
  adj=[[] for _ in range(n)]
  for i,j in edges:adj[j if reverse else i].append(i if reverse else j)
  while todo:
   for j in adj[todo.pop()]:
    if j not in seen:seen.add(j);todo.append(j)
  if len(seen)!=n:return False
 return True
def ap(n,a):
 return (all(any(i==k and s==1 for i,j,s in a) for k in range(n)) and
         all(any(j==k and s==1 for i,j,s in a) for k in range(n)) and
         strong(n,[(i,j) for i,j,s in a]) and
         strong(n,[(i,j) if s==1 else (j,i) for i,j,s in a]))
def minimal(n,a):return ap(n,a) and all(not ap(n,a[:k]+a[k+1:]) for k in range(len(a)))
if __name__=='__main__':
 random.seed(292);start=time.monotonic();stats=[];witness=None
 for n in range(3,13):
  best=[];valid=0
  for trial in range(1000):
   if time.monotonic()-start>100:break
   a=[(i,j,random.choice([-1,1])) for i in range(n) for j in range(n) if i!=j and random.random()<.65]
   if not ap(n,a):continue
   valid+=1;random.shuffle(a)
   for e in a[:]:
    b=a.copy();b.remove(e)
    if ap(n,b):a=b
   assert minimal(n,a)
   if len(a)>len(best):best=a
   if len(a)>2*n-2:witness=dict(n=n,arcs=a);break
  stats.append(dict(n=n,valid_trials=valid,best_size=len(best),bound=2*n-2,best=best))
  if witness or time.monotonic()-start>100:break
 result=dict(mechanism='two-digraph greedy minimality; tests finite obstruction conjecture, not universal proof',seed=292,stats=stats,witness=witness,seconds=time.monotonic()-start)
 (L/'checks-result.json').write_text(json.dumps(result,indent=2)+'\n');print(json.dumps(result))
