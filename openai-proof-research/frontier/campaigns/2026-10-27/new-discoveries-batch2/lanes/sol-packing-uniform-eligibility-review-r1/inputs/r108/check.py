from pathlib import Path
from functools import lru_cache
from itertools import permutations,combinations
import json,time
L=Path(__file__).parent;start=time.monotonic();calls=0;maxstates=0
def count(pi,m,j):
 global calls,maxstates
 K=len(pi);d=K-m;n=K+(j-1)*d;pred=[0]*n;order=sorted(range(K),key=lambda i:pi[i])
 for q in range(j):
  for a,b in zip(order,order[1:]):pred[q*d+b]|=1<<(q*d+a)
 full=(1<<n)-1
 @lru_cache(None)
 def rec(S):
  if rec.cache_info().currsize>120000:raise RuntimeError('120000 ideal-state cap')
  if S==full:return 1
  z=0
  for i in range(n):
   if not(S>>i&1) and pred[i]&S==pred[i]:z+=rec(S|1<<i)
  return z
 z=rec(0);maxstates=max(maxstates,rec.cache_info().currsize);calls+=1;return z
def rank(t):return tuple(sorted(t).index(x) for x in t)
# Exact source model regression from public refutation, no novelty claim.
assert count((1,3,4,7,2,5,6,8),4,2)==9
assert count((1,3,5,7,2,4,6,8),4,2)==8
rows=[];groups={};collisions=0
for K in range(2,6):
 for pi in permutations(range(1,K+1)):
  for m in range(1,K):
   if rank(pi[:m])!=rank(pi[-m:]):continue
   seq=tuple(count(pi,m,j) for j in range(1,8))
   key=seq[:5]
   if key in groups and groups[key]['seq']!=seq:collisions+=1;rows.append({'different_after5':[groups[key],{'pi':pi,'m':m,'seq':seq}]})
   else:groups[key]={'pi':pi,'m':m,'seq':seq}
print('cutoff',calls,len(groups),collisions,flush=True)
(L/'cutoff-check.json').write_text(json.dumps({'K_max':5,'j_max':7,'calls':calls,'distinct_prefixes':len(groups),'splits_after5':rows,'proof':False},indent=2))
# Item6: enumerate only increasing boundary patterns with sorted middle;
# full class not exhausted and no existential conclusion is extrapolated.
w=[];searched=0
for K,m in [(7,3),(8,3),(9,4)]:
 found=None
 for A in combinations(range(1,K+1),m):
  if found:break
  for B in combinations([x for x in range(1,K+1) if x not in A],m):
   pi=A+tuple(x for x in range(1,K+1) if x not in A+B)+B;searched+=1
   if count(pi,m,2)!=3:continue
   seq=tuple(count(pi,m,j) for j in range(1,6))
   if seq==(1,3,15,105,945):found={'K':K,'m':m,'pi':pi,'seq':seq};w.append(found);break
 print('item6',K,m,found,flush=True)
(L/'check-results.json').write_text(json.dumps({'calls':calls,'max_ideal_states':maxstates,'item6_tested':searched,'item6_finite_matches':w,'wall_seconds':time.monotonic()-start,'limits':{'ideal_states':120000,'K_cutoff':5,'j_cutoff':7},'source_claim_proved':False},indent=2))
print('DONE',calls,maxstates,flush=True)
