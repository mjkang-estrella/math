# Block strategies: m distinct positive integer levels x1>...>xm (<=V), block sizes n1..nm, n0 zeros.
# Light k-sets: weight <= T. Compare with best uniform at d -> (sum c / T)^-.
import sys,json,itertools
from math import comb
n,k,m,V=map(int,sys.argv[1:5])
def comps(total,parts):
  if parts==0:
    if total>=0: yield ()
    return
  for a in range(1,total+1):
    for rest in comps(total-a,parts-1): yield (a,)+rest
U_cache={}
def uniform_best(T,S):
  key=(T,S)
  if key not in U_cache:
    U_cache[key]=max(sum(comb(r,j)*comb(n-r,k-j) for j in range(0,min(k,(r*T)//S)+1)) for r in range(1,n+1))
  return U_cache[key]
viol=[]; checked=0
for sizes in [s for tot in range(m,n+1) for s in comps(tot,m)]:
  n0=n-sum(sizes)
  # all count vectors
  vecs=[]
  for sv in itertools.product(*[range(min(sz,k)+1) for sz in sizes]):
    t=sum(sv)
    if t<=k and k-t<=n0:
      w=comb(n0,k-t)
      for b,sb in enumerate(sv): w*=comb(sizes[b],sb)
      vecs.append((sv,w))
  for xs in itertools.combinations(range(V,0,-1),m):
    S=sum(x*sz for x,sz in zip(xs,sizes))
    sums={}
    for sv,w in vecs:
      s=sum(a*b for a,b in zip(sv,xs)); sums[s]=sums.get(s,0)+w
    keys=sorted(sums); acc=0
    for s in keys:
      acc+=sums[s]
      if s>=S: break
      T=s; checked+=1
      # light family = weight <= T; achievable for d < S/T
      if acc>uniform_best(T,S): viol.append(dict(sizes=sizes,zeros=n0,levels=xs,T=T,D=f"{S}/{T}",light=acc,uniform=uniform_best(T,S)))
print(json.dumps(dict(n=n,k=k,m=m,V=V,checked=checked,violations=len(viol),examples=viol[:8])))
