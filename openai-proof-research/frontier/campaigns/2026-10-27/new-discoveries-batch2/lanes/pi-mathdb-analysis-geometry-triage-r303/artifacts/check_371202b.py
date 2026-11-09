"""371202 with bi-infinite minimum. Empirical natural density over uniform box vs claimed P(n)."""
import math, random
random.seed(7)
def argmin_bi(a0,a1):
    # forward: a_{n}=a_{n-1}+a_{n-2}; backward: a_{n-2}=a_n-a_{n-1}
    fwd=[abs(a0),abs(a1)]; f=[a0,a1]; i=1
    best=fwd[0]; bi=0
    while True:
        i+=1; v=abs(f[0]+f[1]); f=[f[1],f[0]+f[1]]; fwd.append(v)
        if v<best: best=v; bi=i
        if i>10 and v>4*best and v>2*fwd[i-2] and v>10**9: break
    bwd=[abs(a0),abs(a1)]; g=[a0,a1]; j=1
    while True:
        j+=1; v=abs(g[1]-g[0]); g=[g[1]-g[0],g[0]]  # a_{n-2}=a_n-a_{n-1}; new pair (a_{n-1},a_{n-2})
        bwd.append(v)
        if v<best: best=v; bi=-j+1
        if j>10 and v>4*best and v>2*bwd[j-2] and v>10**9: break
    return bi
N=400000
cnt={}
for _ in range(N):
    a0=random.randint(-3000,3000); a1=random.randint(-3000,3000)
    bi=argmin_bi(a0,a1); cnt[bi]=cnt.get(bi,0)+1
def P_formula(n):
    L=[2,1]
    while len(L)<n+4: L.append(L[-1]+L[-2])
    if n==0: return 1/4
    if n>1 and n%2==0: return (math.atan(L[n-2]/L[n-1])-math.atan(L[n]/L[n+1]))/math.pi
    if n>1 and n%2==1: return (math.atan(L[n]/L[n+1])-math.atan(L[n-2]/L[n-1]))/math.pi
    if n==1: return None
print("n : empirical : formula : diff")
for n in list(range(-8,9)):
    emp=cnt.get(n,0)/N
    f=P_formula(n) if n>=0 else P_formula(1-n)
    print(n, f"{emp:.6f}", (f"{f:.6f} diff={emp-f:+.2e}" if f is not None else "n=1 undef"))
print("P(1) empirical:", cnt.get(1,0)/N)
