# Exact certificate for the 368940 proof: on a 7-element set, a function Phi on 3-subsets
# is recovered from the 4-subset sums S(Q)=sum_{T in Q} Phi(T) by
# Phi(T0)=sum_Q c_{|Q cap T0|} S(Q), c_3=1/4, c_2=-1/12, c_1=1/12, c_0=-1/4.
from itertools import combinations
from fractions import Fraction as F
import random, math, sys
V=range(7); T3=list(combinations(V,3)); Q4=list(combinations(V,4))
c={3:F(1,4),2:F(-1,12),1:F(1,12),0:F(-1,4)}
ok=True
for T0 in T3:
    for T in T3:
        coeff=sum(c[len(set(Q)&set(T0))] for Q in Q4 if set(T)<=set(Q))
        ok &= coeff==(1 if T==T0 else 0)
print('explicit inverse identity on all 35x35 pairs:',ok)
# Independent rank check of inclusion matrix W_{3,4}(7) by exact elimination.
M=[[F(int(set(T)<=set(Q))) for Q in Q4] for T in T3]; r=0
for col in range(35):
    p=next((i for i in range(r,35) if M[i][col]!=0),None)
    if p is None: continue
    M[r],M[p]=M[p],M[r]
    for i in range(35):
        if i!=r and M[i][col]!=0:
            f=M[i][col]/M[r][col]; M[i]=[a-f*b for a,b in zip(M[i],M[r])]
    r+=1
print('rank W_{3,4}(7) =',r)
# Illustration only (not part of proof): the incenter X1 violates the identity on a random convex cyclic quadrilateral.
random.seed(1); ang=sorted(random.uniform(0,2*math.pi) for _ in range(4)); P=[(math.cos(a),math.sin(a)) for a in ang]
def inc(a,b,c):
    la=math.dist(b,c); lb=math.dist(a,c); lc=math.dist(a,b); s=la+lb+lc
    return ((la*a[0]+lb*b[0]+lc*c[0])/s,(la*a[1]+lb*b[1]+lc*c[1])/s)
E=[inc(*[P[j] for j in range(4) if j!=i]) for i in range(4)]
m=lambda pts:(sum(p[0] for p in pts)/4,sum(p[1] for p in pts)/4)
print('incenter illustration centroid gap:',math.dist(m(P),m(E)))
sys.exit(0 if ok and r==35 else 1)
