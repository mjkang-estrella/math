"""Exact natural-density computation via angular measure. Sequence a_k = F_{k-1} a0 + F_k a1 (k>=1), a_0=a0,
backward a_{-1}=a1-a0, a_{-2}=2a0-a1, ... a_{-j} = (-1)^{j-1}(F_{j-1} a0? ) -- compute directly by iteration.
For each angle theta, direction u=(c,s); a_k = t*(coeff_k) linear in t; min position of |coeff_k| over k in Z.
Density of position n = angular measure / (2*pi). Vectorized chunked."""
import numpy as np, math
M=2**22
F=[0,1]
while len(F)<90: F.append(F[-1]+F[-2])
# coefficients: forward k>=0: a_k = F_{k-1} a0 + F_k a1 (F_{-1}=1)
# backward: a_{-1}=a1-a0; a_{-2}=a0-a_{-1}=2a0-a1; a_{-3}=a_{-1}-a_{-2}=2a1-3a0; a_{-4}=a_{-2}-a_{-3}=3a0-5a1...
# general: a_{-j} = (-1)^{?}(F_j a0 - F_{j+1} a1)? check: j=1: a_{-1}=a1-a0 -> -(F_1 a0 - F_2 a1)=-(a0-a1) ok sign
# a_{-j} = (-1)^j (F_j a0 - F_{j+1} a1)? j=1: -(a0-a1)=a1-a0 ok. j=2: +(2a0-a1)? F_2=1,F_3=2 -> a0-2a1 no.
# just iterate numerically per chunk in float; growth phi^j, need j up to ~80 for 1e-16 precision; use float128? use longdouble.
def coeffs(jmax=110):
    cf=[]
    a,b=np.longdouble(1),np.longdouble(0)  # a_{-1}=a1-a0 -> coeff (−1,1); iterate backward from (a0,a1)
    # backward recurrence: a_{n-2}=a_n-a_{n-1}; keep (a_{n-1},a_n) -> next (a_{n-2},a_{n-1})
    # represent as coeff pairs (ca,cb) s.t. a = ca*a0+cb*a1
    cur=[(1,0),(0,1)]  # a0,a1
    for j in range(1,jmax):
        (c1a,c1b),(c2a,c2b)=cur[-1],cur[-2]  # a_{n-1},a_n
        cur.append((c2a-c1a,c2b-c1b))  # a_{n-2}
    back=cur[2:]  # a_{-1}, a_{-2}, ...
    fwd=[(F[k-1] if k>=1 else 1, F[k] if k>=1 else 0) for k in range(0,80)]
    return fwd+back  # positions 0..79, then -1,-2,...
CF=coeffs()
pos=[]
K=len(CF)
cnt=np.zeros(K,dtype=np.int64)
for start in range(0,M,2**20):
    th=(np.arange(start,min(start+2**20,M))+0.5)*(2*np.pi/M)
    c=np.cos(th,dtype=np.float64); s=np.sin(th,dtype=np.float64)
    vals=np.empty((len(th),K))
    for idx,(ca,cb) in enumerate(CF):
        vals[:,idx]=np.abs(ca*c+cb*s)
    am=np.argmin(vals,axis=1)
    # map index -> position
    posmap=np.array([i if i<80 else -(i-80+1) for i in range(K)])
    p=posmap[am]
    for q in np.unique(p):
        cnt[posmap.tolist().index(q) if False else 0]=0
    # use dict
    u,c2=np.unique(p,return_counts=True)
    for uu,cc in zip(u,c2): cnt[0]+=0
    if start==0:
        global_counts={}
    for uu,cc in zip(u,c2): global_counts[int(uu)]=global_counts.get(int(uu),0)+int(cc)
tot=M
print("position : exact-density : formula")
def P_formula(n):
    L=[2,1]
    while len(L)<n+4: L.append(L[-1]+L[-2])
    if n==0: return 0.25
    if n%2==1: return (math.atan(L[n]/L[n+1])-math.atan(L[n-2]/L[n-1]))/math.pi
    return (math.atan(L[n-2]/L[n-1])-math.atan(L[n]/L[n+1]))/math.pi
for n in range(-8,9):
    emp=global_counts.get(n,0)/tot
    f=P_formula(n) if n>=0 else P_formula(1-n)
    print(n, f"{emp:.7f}", f"{f:.7f}", f"diff={emp-f:+.2e}")
