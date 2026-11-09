# Grundy values of path runs with boundary conditions.
# A: free-free, B: free-forced, C: forced-forced coherent, D: forced-forced incoherent
from functools import lru_cache
def mex(s):
    g=0
    while g in s: g+=1
    return g
N=60
A=[0]*(N+1);B=[0]*(N+1);C=[0]*(N+1);D=[0]*(N+1)
for k in range(1,N+1):
    # A
    s=set()
    for j in range(1,k+1):
        s.add(B[j-1]^B[k-j])
    A[k]=mex(s)
    # B: left free, right forced R
    s=set()
    for j in range(1,k+1):
        for d in 'RL':
            if j==k and d!='R': continue
            right = 0 if j==k else (C[k-j] if d=='R' else D[k-j])
            s.add(B[j-1]^right)
    B[k]=mex(s)
    # C: forced R both
    s=set()
    for j in range(1,k+1):
        for d in 'RL':
            if (j==1 or j==k) and d!='R': continue
            if d=='R': s.add(C[j-1]^C[k-j])
            else: s.add(D[j-1]^D[k-j])
    C[k]=mex(s)
    # D: left forced R, right forced L
    s=set()
    for j in range(1,k+1):
        for d in 'RL':
            if j==1 and d!='R': continue
            if j==k and d!='L': continue
            if d=='R': s.add(C[j-1]^D[k-j])
            else: s.add(D[j-1]^C[k-j])
    D[k]=mex(s)
for name,X in zip('ABCD',(A,B,C,D)):
    print(name, X)
