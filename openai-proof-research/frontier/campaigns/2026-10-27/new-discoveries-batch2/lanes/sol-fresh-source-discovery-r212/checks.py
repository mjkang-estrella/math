from fractions import Fraction as F
from collections import defaultdict
import random,json
def model(r,c):
 k=int(r//c);return 3*c*(2**k-1)+3*(r-k*c)*2**k
def events(n,edges,root,T):
 out=[[] for _ in range(n)];dest=[];length=[]
 for i,(a,b,l) in enumerate(edges):
  out[a].append(2*i);out[b].append(2*i+1);dest.extend([b,a]);length.extend([l,l])
 dp=[defaultdict(int) for _ in range(T+1)]
 for e in out[root]:
  if length[e]<=T:dp[length[e]][e]+=1
 ev=defaultdict(int)
 for d in range(1,T+1):
  for e,num in dp[d].items():
   ev[d]+=num
   for f in out[dest[e]]:
    t=d+length[f]
    if f!=(e^1) and t<=T:dp[t][f]+=num
 return ev
def volume(ev,r):return 3*r+sum(num*(r-d) for d,num in ev.items() if d<r)
def connected(n,edges):
 seen={0}
 while True:
  new=seen|{b for a,b,l in edges if a in seen}|{a for a,b,l in edges if b in seen}
  if new==seen:return len(seen)==n
  seen=new
def run():
 rng=random.Random(212);cases=0;comparisons=0;bad_roots=0;counterexamples=[];witness=None
 for n in [2,4,6,8,10,12]:
  for _ in range(120):
   stubs=list(range(n))*3;rng.shuffle(stubs);edges=[(stubs[i],stubs[i+1],rng.randrange(2,10)) for i in range(0,len(stubs),2)]
   if not connected(n,edges):continue
   c=F(sum(e[2] for e in edges),len(edges));T=int(6*c)+1
   evs=[events(n,edges,v,T) for v in range(n)]
   radii=sorted({F(0),6*c}|{F(d) for ev in evs for d in ev if d<=6*c}|{k*c for k in range(7)})
   good=[True]*n
   for r in radii:
    bs=[volume(ev,r) for ev in evs];m=model(r,c)
    assert sum(bs)>=n*m,('average',n,edges,str(r))
    comparisons+=1
    for v,b in enumerate(bs):
     if b<m:
      if good[v]:bad_roots+=1
      good[v]=False
      if witness is None:witness={'n':n,'edges':edges,'root':v,'radius':str(r),'ball':str(b),'model':str(m),'lambda':str(c)}
   if not any(good):counterexamples.append({'n':n,'edges':edges})
   cases+=1
 # Independent branch recurrence versus event formula on rational theta edges.
 from functools import lru_cache
 @lru_cache(None)
 def branch(i,r):
  ell=[2,3,4][i]
  return min(r,ell)+(sum(branch(j,r-ell) for j in range(3) if j!=i) if r>ell else 0)
 theta=[(0,1,2),(0,1,3),(0,1,4)]
 ev=events(2,theta,0,30)
 for j in range(61):
  r=F(j,2);assert volume(ev,r)==sum(branch(i,r) for i in range(3))
 # Source equality Example7.2: normalized lengths 2/3,1,4/3 at radius4/3.
 assert volume(ev,F(4))/3==model(F(4,3),F(1))
 print(json.dumps({'seed':212,'connected_cubic_cases':cases,'radii_through_six_lambda':comparisons,'roots_failing_some_radius':bad_roots,'common_root_counterexamples':counterexamples,'first_bad_root':witness,'independent_theta_recurrence_checks':61,'status':'finite diagnostics only; no universal proof'},sort_keys=True))
if __name__=='__main__':run()
