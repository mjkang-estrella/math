# Independent brute-force cross-check for zerosum.rs: all multisets over Z_n of size n+k with
# h(S)<=k, testing every n-subsequence directly (itertools.combinations on index positions).
import itertools,sys
def run(n,k,cap=None):
  cap=k if cap is None else cap
  cnt=0;ex=[]
  for S in itertools.combinations_with_replacement(range(n),n+k):
    if max(S.count(x) for x in set(S))>cap: continue
    if S.count(0)<max(S.count(x) for x in set(S)): continue  # same normalisation: 0 has max multiplicity
    if not any(sum(c)%n==0 for c in itertools.combinations(S,n)):
      cnt+=1; ex.append(S)
  return cnt,ex[:3]
for n,k,c in [(4,2,2),(6,2,2),(6,3,3),(6,4,4),(8,2,2),(8,3,3),(9,3,3),(4,2,3),(6,3,5),(6,4,5),(6,2,5),(8,3,7)]:
  r=run(n,k,c); print(n,k,c,r[0],r[1][:2],flush=True)
