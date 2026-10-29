from itertools import product,permutations
from collections import Counter
import json,math
def data(n,edges,gains,mask,q=2):
 adj=[[] for _ in range(n)];count=0
 for i,(u,v) in enumerate(edges):
  if mask>>i&1:
   count+=1;adj[u].append((v,gains[i]));adj[v].append((u,-gains[i]))
 pot={};components=0;balanced=True
 for u in range(n):
  if u in pot:continue
  components+=1;pot[u]=0;stack=[u]
  while stack:
   v=stack.pop()
   for w,a in adj[v]:
    val=(pot[v]+a)%q
    if w in pot:balanced &= pot[w]==val
    else:pot[w]=val;stack.append(w)
 return n-components,balanced,count
cases=axiom_checks=0
for n,edges in [(4,[(i,j) for i in range(4) for j in range(i+1,4)]),(2,[(0,1),(0,1),(0,0),(1,1)]),(1,[(0,0),(0,0)])]:
 m=len(edges);fullrank=data(n,edges,[0]*m,(1<<m)-1)[0]
 for gains in product(range(2),repeat=m):
  if any(u==v and gains[i]==0 for i,(u,v) in enumerate(edges)):continue
  d=[data(n,edges,gains,s) for s in range(1<<m)]
  ranks=[d[s&((1<<m)-1)][0]+int(bool(s>>m) or not d[s&((1<<m)-1)][1]) for s in range(1<<(m+1))]
  assert ranks[0]==0
  for a in range(len(ranks)):
   assert ranks[a]<=a.bit_count()
   for b in range(len(ranks)):
    assert ranks[a]+ranks[b]>=ranks[a|b]+ranks[a&b];axiom_checks+=1
  tau=Counter();chi=Counter()
  for s,(r,bal,cnt) in enumerate(d):
   sign=(-1)**cnt
   if bal:tau[fullrank-r]+=sign
   chi[fullrank+1-r-int(not bal)]+=sign
   chi[fullrank-r]-=sign
  rhs=Counter()
  for k,v in tau.items():rhs[k+1]+=v;rhs[k]-=v
  assert all(chi[k]==rhs[k] for k in set(chi)|set(rhs))
  w=[(-1)**i*tau[fullrank-i] for i in range(fullrank+1)]
  assert all(v>0 for v in w)
  assert all(w[i]**2>=w[i-1]*w[i+1] for i in range(1,len(w)-1));cases+=1
# A faithful cyclic permutation action need not have a regular orbit.
p=(0,2,1,4,5,3)
def order(p):
 ans=1;seen=set();lengths=[]
 for i in range(len(p)):
  if i in seen:continue
  j=i;k=0
  while j not in seen:seen.add(j);k+=1;j=p[j]
  lengths.append(k);ans=math.lcm(ans,k)
 return ans,lengths
o,lens=order(p);assert o==6 and lens==[1,2,3] and max(lens)<o
bad2=[i for i in range(6) if p[p[p[i]]]==i]
bad3=[i for i in range(6) if p[p[i]]==i]
assert set(bad2)|set(bad3)==set(range(6)) and p[0]==0
print(json.dumps({'gain_cases':cases,'rank_submodular_pairs':axiom_checks,'char_identity':'PASS','finite_logconcavity':'PASS; not universal proof','generic_regular_orbit_falsifier':{'permutation':p,'order':o,'cycles':lens,'fix_cube':bad2,'fix_square':bad3},'source_counterexample':False}))
