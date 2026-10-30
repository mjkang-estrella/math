"""Exact bounded diagnostics only. Run under the specified helper_guard.py."""
import itertools, json, sys
from pathlib import Path
sys.setrecursionlimit(10000)
L=Path(__file__).resolve().parent
def score(a,b):return sum(x>y for x in a for y in b)
def target(n):return n*n//2+1
def components(g):
 idx={};low={};stack=[];active=set();out=[]
 def visit(v):
  idx[v]=low[v]=len(idx);stack.append(v);active.add(v)
  for w in g[v]:
   if w not in idx:visit(w);low[v]=min(low[v],low[w])
   elif w in active:low[v]=min(low[v],idx[w])
  if low[v]==idx[v]:
   c=[]
   while True:
    w=stack.pop();active.remove(w);c.append(w)
    if w==v:break
   out.append(c)
 for v in range(len(g)):
  if v not in idx:visit(v)
 return out
results=[]
for n in range(3,8):
 dice=list(itertools.combinations_with_replacement(range(1,n+1),n))
 counts=[tuple(d.count(v) for v in range(1,n+1)) for d in dice]
 higher=[tuple(sum(x>v for x in d) for v in range(1,n+1)) for d in dice]
 g=[[j for j,b in enumerate(counts) if i!=j and sum(x*y for x,y in zip(a,b))==target(n)] for i,a in enumerate(higher)]
 cs=components(g);non=[c for c in cs if len(c)>1]
 result={'n':n,'vertices':len(dice),'edges':sum(map(len,g)),'SCCs':len(cs),'nontrivial_sizes':sorted(map(len,non))}
 # Exhaust all cycles only for n<=6; bounded first-witness DFS for n=7.
 cycles=[];steps=[0];budget=200000
 def dfs(start,path,used,allowed):
  steps[0]+=1
  if steps[0]>budget:return
  v=path[-1]
  if start in g[v] and len(path)>=3:
   cycles.append(path[:])
   if n==7 and len(path)>n:return True
  for w in g[v]:
   if w>start and w in allowed and w not in used:
    if dfs(start,path+[w],used|{w},allowed):return True
 for c in non:
  for start in sorted(c):
   if dfs(start,[start],{start},set(c)) and n==7:break
  if n==7 and any(len(c)>n for c in cycles):break
 result.update(dfs_steps=steps[0],exhaustive_cycles=n<=6,cycle_lengths=sorted(set(map(len,cycles))))
 if cycles:
  cyc=max(cycles,key=len);ds=[dice[i] for i in cyc];result['witness']=ds
  assert all(score(ds[i],ds[(i+1)%len(ds)])==target(n) for i in range(len(ds)))
 if n==6:assert max(map(len,cycles))==6
 if n<=5:assert not non
 results.append(result)
# Verify all pairwise common-low padding identities on all 6-sided dice.
d6=list(itertools.combinations_with_replacement(range(1,7),6))
padding=0
for a in d6:
 for b in d6:
  aa=(1,)+tuple(x+1 for x in a);bb=(1,)+tuple(x+1 for x in b)
  assert score(aa,bb)==score(a,b)+6;padding+=1
# Threshold arithmetic and coprimality checks are controls, not universal proof.
import math
for n in range(3,1001):
 assert math.gcd(target(n),n*n)==1
 if n%2==0:assert target(n+1)-target(n)==n
 else:assert target(n+1)-target(n)==n+1
out={'status':'PASS','graphs':results,'common_low_pair_controls':padding,'threshold_controls':998,'limit':'Finite exact diagnostics; no universal source resolution.'}
# Common-multiset padding cyclic-sum identity, including ties.
identity_controls=0
for n in range(3,8):
 ds=[tuple([1]*(n-1)+[3]),tuple([2]*n),tuple([1]+[4]*(n-1))]
 for r in range(1,5):
  for p in itertools.combinations_with_replacement(range(1,5),r):
   gain=sum(score(ds[i]+p,ds[(i+1)%3]+p)-score(ds[i],ds[(i+1)%3]) for i in range(3))
   ties=sum(sum(x==y for x in d for y in p) for d in ds)
   assert gain==3*(n*r+score(p,p))-ties
   if r>=2 or n%2:assert target(n+r)-target(n)>n*r+r*(r-1)//2
   identity_controls+=1
out['common_multiset_identity_controls']=identity_controls
(L/'checks.json').write_text(json.dumps(out,indent=2)+'\n')
print(json.dumps({k:v for k,v in out.items() if k!='graphs'}))
