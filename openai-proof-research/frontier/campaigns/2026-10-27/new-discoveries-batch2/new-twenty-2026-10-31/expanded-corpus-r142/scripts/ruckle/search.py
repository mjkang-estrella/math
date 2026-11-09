# Search for counterexamples to Ruckle's conjecture (one-shot accumulation game).
# Hider strategy: integer weights c1>=...>=cn>=0, threshold T; light k-sets: sum_S c <= T.
# Achieves >= #light light sets for every d < D* = sum(c)/T (scale by (1-eps)/T).
# Uniform-r best at d -> D*^- : light_r = sum_{j<=floor(r*T/sum c)} C(r,j)C(n-r,k-j).
import sys,json,itertools
from math import comb
n,k,M=map(int,sys.argv[1:4])
def light_counts(c):
  # dp[j][s] = number of j-subsets with sum s
  S=sum(c); dp=[[0]*(S+1) for _ in range(k+1)]; dp[0][0]=1
  for x in c:
    for j in range(k,0,-1):
      row=dp[j]; prev=dp[j-1]
      for s in range(S,x-1,-1): row[s]+=prev[s-x]
  cum=[0]*(S+1); acc=0
  for s in range(S+1): acc+=dp[k][s]; cum[s]=acc
  return cum
best=[]; checked=0
def gen(i,maxv,acc):
  if i==n: yield tuple(acc); return
  for v in range(maxv,-1,-1):
    acc.append(v); yield from gen(i+1,v,acc); acc.pop()
for c in gen(0,M,[]):
  S=sum(c)
  if S==0 or c[0]==0: continue
  cum=light_counts(list(c))
  for T in range(1,S):
    L=cum[T] if T<=S else comb(n,k)
    checked+=1
    U=max(sum(comb(r,j)*comb(n-r,k-j) for j in range(0,min(k,(r*T)//S)+1)) for r in range(1,n+1))
    if L>U: best.append(dict(c=c,T=T,D=f"{S}/{T}",light=L,uniform_best=U))
print(json.dumps(dict(n=n,k=k,M=M,checked=checked,violations=len(best),examples=best[:10])))
