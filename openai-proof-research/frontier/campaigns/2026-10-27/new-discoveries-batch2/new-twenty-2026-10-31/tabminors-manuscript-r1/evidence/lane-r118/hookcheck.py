"""Check mM_k(hook w) = k! * sum_{P, |P|=N-k} min(P) [hook(w_P)] against exact DP (verify_minors.mm)."""
import sys, itertools, math
from collections import Counter
sys.path.insert(0,'scripts'); from verify_minors import mm
def hook(w):  # w: string over A/L for entries 2..n
    arm=[1]+[i+2 for i,c in enumerate(w) if c=='A']; legs=[(i+2,) for i,c in enumerate(w) if c=='L']
    return tuple([tuple(arm)]+legs)
def formula(w,k):
    N=len(w); C=Counter()
    for P in itertools.combinations(range(1,N+1),N-k):
        C[hook(''.join(w[p-1] for p in P))]+=math.factorial(k)*(P[0] if P else 1)
    return C
import random; random.seed(1); bad=0; tested=0
for N in range(3,10):
    for _ in range(12):
        w=''.join(random.choice('AL') for _ in range(N))
        for k in range(1,N):
            A=dict(mm(hook(w),k)); B=dict(formula(w,k)); tested+=1
            if A!=B: bad+=1; print('MISMATCH',w,k)
print('formula checks',tested,'mismatches',bad)
