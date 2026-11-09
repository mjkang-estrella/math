"""Exact bounded method controls. No floating point and no source resolution."""
from fractions import Fraction as F
from itertools import combinations
import random,json
from math import comb
def eye(n):return [[F(i==j) for j in range(n)] for i in range(n)]
def mul(a,b):return [[sum(x*y for x,y in zip(r,c)) for c in zip(*b)] for r in a]
def inv(a):
 n=len(a);a=[r[:]+s for r,s in zip(a,eye(n))]
 for j in range(n):
  k=next((k for k in range(j,n) if a[k][j]),None)
  if k is None:raise ValueError('singular')
  a[j],a[k]=a[k],a[j];v=a[j][j];a[j]=[x/v for x in a[j]]
  for k in range(n):
   if k!=j:
    v=a[k][j];a[k]=[x-v*y for x,y in zip(a[k],a[j])]
 return [r[n:] for r in a]
def norm(a):return max(sum(map(abs,r)) for r in a)
def pack(p):
 N=len(p);t=2-norm(p);good={}
 for a in range(1,1<<N):
  for k in range(N):
   if a>>k&1 and sum(abs(p[k][j]) for j in range(N) if a>>j&1)>=t:good[a]=k;break
 # Inclusion-minimal good sets suffice for maximum packing.
 mins=[a for a in good if not any(b!=a and b&a==b for b in good)]
 dp={0:[]}
 for a in mins:
  for mask,sol in list(dp.items()):
   if not mask&a and len(sol)+1>len(dp.get(mask|a,[])):dp[mask|a]=sol+[a]
 sol=max(dp.values(),key=len)
 return sol,good,mins
def run():
 rng=random.Random(215);accepted=0;tested=0;bad_greedy=[];coord_fail=0
 for n in [2,3,4]:
  N=2*n;p0=[[F(1,2) if i//2==j//2 else F(0) for j in range(N)] for i in range(N)]
  for rep in range(45):
   tested+=1;s=eye(N);den=rng.choice([80,120,180,240])
   for i in range(N):
    for j in range(N):s[i][j]+=F(rng.randrange(-2,3),den)
   try:p=mul(mul(s,p0),inv(s))
   except ValueError:continue
   assert mul(p,p)==p
   L=norm(p)
   if L>=F(4,3):continue
   accepted+=1;sol,good,mins=pack(p);assert len(sol)==n
   for a in sol:assert sum(abs(p[good[a]][j]) for j in range(N) if a>>j&1)>=2-L
   # Try many maximal matchings; failure would falsify the no-exchange shortcut.
   for _ in range(10):
    rng.shuffle(mins);used=0;g=[]
    for a in mins:
     if not a&used:g.append(a);used|=a
    if len(g)<n:bad_greedy.append(dict(n=n,L=str(L),sets=g));break
   # Separate coordinate-minor route, tested with an explicit range basis.
   u=[[s[i][2*j]+s[i][2*j+1] for j in range(n)] for i in range(N)]
   best=None
   for I in combinations(range(N),n):
    try:c=norm(mul(u,inv([u[i] for i in I])))
    except ValueError:continue
    best=c if best is None else min(best,c)
   if best>L/(4-3*L):coord_fail+=1
 # Actual source Proposition3.4: exact idempotence and row norms.
 u=[F(1),F(4,5),F(1,4),-F(1,4),-F(4,5)];v=[F(0),F(3,5),F(1),F(1),F(3,5)]
 f=[F(2,3),F(1,6),F(2,15),-F(2,15),-F(1,6)];g=[F(0),F(1,6),F(2,5),F(2,5),F(1,6)]
 q=[[u[i]*f[j]+v[i]*g[j] for j in range(5)] for i in range(5)]
 assert mul(q,q)==q and norm(q)==F(13,10)
 p=[r+[F(0)] for r in q]+[[F(0)]*5+[F(1)]]
 assert len(pack(p)[0])==3
 source_pack=pack(p)[0];source_random=0;source_greedy=[]
 for rep in range(240):
  s=eye(6);den=rng.choice([200,400,800])
  for i in range(6):
   for j in range(6):s[i][j]+=F(rng.randrange(-2,3),den)
  z=mul(mul(s,p),inv(s));assert mul(z,z)==z
  if norm(z)>=F(4,3):continue
  source_random+=1;sol,good,mins=pack(z);assert len(sol)==3
  for _ in range(12):
   rng.shuffle(mins);used=0;greedy=[]
   for a in mins:
    if not a&used:greedy.append(a);used|=a
   if len(greedy)<3:
    source_greedy.append(dict(rep=rep,norm=str(norm(z)),sets=greedy,
                              maximum=sol,matrix=[[str(x) for x in r] for r in z]));break
 # Determinant route uniform inverse conditioning fails even at contractive projections.
 for N in [6,10,20]:
  a=[[F(i==j)-F(1,N) for j in range(N-1)] for i in range(N-1)]
  assert norm(inv(a))==N
 # Weighted-inverse sufficient bound fails for arbitrary nonminimal projections.
 N=20;eps=F(1,10);f=[F(21,200)]*10+[-F(1,200)]*10
 assert sum(f)==1 and sum(map(abs,f))==1+eps
 weighted=[]
 for k in range(N):
  S=[j for j in range(N) if j!=k]
  z=[[F(i==j)-f[j] for j in S] for i in S]
  weighted.append(eps*norm(inv(z)))
 assert min(weighted)>4*eps/(1-3*eps)
 # Full proof of the cut-cube family is in discovery.md; these are arithmetic controls only.
 for n in range(3,31):
  c=sum(F(comb(n,k)*abs(n-2*k),2**n) for k in range(n+1))
  assert c>=F(3,2)
  for a in [F(101,100),F(6,5),F(13,10)]:
   for alpha in [F(j,10) for j in range(-10,21)]:assert a*abs(alpha)+c*abs(1-alpha)>=a
 return dict(seed=215,attempted=tested,eligible=accepted,all_maximum_packings_pass=True,
             greedy_failures=bad_greedy,coordinate_certificate_failures=coord_fail,
             source_W3_norm='13/10',inverse_conditioning_counterchecks=[6,10,20],
             source_W3_packing=source_pack,source_perturbations=source_random,
             source_greedy_failures=source_greedy[:1],source_greedy_failure_count=len(source_greedy),
             signed_rank_one_min_weighted_inverse=str(min(weighted)),weighted_goal=str(4*eps/(1-3*eps)),
             scope='Finite rational perturbations only; no universal conclusion')
if __name__=='__main__':print(json.dumps(run(),sort_keys=True))
