"""Exact integer diagnostics. Bounded searches, never universal certificates."""
import itertools, math, json, random, time
from pathlib import Path
P=Path(__file__).resolve().parent
out={'scope':'bounded exact diagnostics only','runner':[],'matching':[]}
def zero_count(a):
 if sum(a)%2:return 0
 target=sum(a)//2; d=[0]*(target+1);d[0]=1
 for x in a:
  for j in range(target,x-1,-1):d[j]+=d[j-x]
 return d[target]
for k in range(4,13):
 cand=tuple(sorted(([2,2]+[1]*(k-2)) if k%2==0 else ([2,2,2]+[1]*(k-3))))
 if k==5:continue
 top=tuple(sorted([1]*k if k%2==0 else [2]+[1]*(k-1)))
 threshold=zero_count(cand);n=0;ties=[];beat=[]
 for a in itertools.combinations_with_replacement(range(1,9),k):
  if math.gcd(*a)!=1:continue
  n+=1;c=zero_count(a)
  if a!=cand and c==threshold:ties.append(a)
  if a!=top and c>threshold:beat.append((a,c))
 out['runner'].append(dict(k=k,max_part=8,primitive_partitions_tested=n,candidate=cand,candidate_zero_count=threshold,denominator=2**k,other_ties=ties,nonleader_exceeds=beat))
def cp(p):
 t=1;df=1
 while p>=(2*t+1)*df:t+=1;df*=2*t-1
 return t*t-t+p//df-1
# Matchings counted by the least remaining vertex recurrence; memo bounded by 2^n per graph.
def match(adj):
 memo={0:1}
 def f(mask):
  if mask in memo:return memo[mask]
  i=(mask&-mask).bit_length()-1;rest=mask^(1<<i);poss=adj[i]&rest;total=0
  while poss:
   b=poss&-poss;poss-=b;total+=f(rest^b)
  memo[mask]=total;return total
 return f((1<<len(adj))-1)
def check(n,deleted):
 adj=[((1<<n)-1)^(1<<i) for i in range(n)]
 for i,j in deleted:adj[i]^=1<<j;adj[j]^=1<<i
 p=match(adj);ex=n*(n-1)//2-len(deleted)-n*n//4
 return p,ex,ex-cp(p) if p else None
for n,depth in [(6,6),(8,4)]:
 edges=list(itertools.combinations(range(n),2));tested=0;best=-999;wit=None;viol=[]
 for d in range(depth+1):
  for deleted in itertools.combinations(edges,d):
   p,e,g=check(n,deleted);tested+=1
   if g is not None and g>best:best=g;wit=dict(n=n,deleted=deleted,p=p,excess=e,Cp=cp(p))
   if g is not None and g>0:viol.append(wit)
 out['matching'].append(dict(n=n,scope=f'all labelled complements with <= {depth} missing edges',tested=tested,max_excess_minus_Cp=best,witness=wit,violations=viol))
rng=random.Random(321549)
for n in [8,10,12,14]:
 edges=list(itertools.combinations(range(n),2));best=-999;wit=None;viol=[]
 for _ in range(5000):
  d=rng.randrange(len(edges)//2+1);deleted=rng.sample(edges,d);p,e,g=check(n,deleted)
  if g is not None and g>best:best=g;wit=dict(n=n,deleted=deleted,p=p,excess=e,Cp=cp(p))
  if g is not None and g>0:viol.append(wit)
 out['matching'].append(dict(n=n,scope='5000 seeded random dense labelled graphs; sampling only',seed=321549,max_excess_minus_Cp=best,witness=wit,violations=viol))
(P/'diagnostics.json').write_text(json.dumps(out,indent=2));print(json.dumps(out,indent=2))
