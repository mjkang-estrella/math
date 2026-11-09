# For given n and integer lambda: float distance of nearest eigenvalues of A=NN^T-4I to lambda (via Gram),
# and exact nullity of (G - (lambda+4) I) modulo two primes (upper bound on multiplicity over Q).
import sys, numpy as np
sys.path.insert(0,__import__('os').path.dirname(__file__))
from queens import gram
def nullity_mod(M,p):
    M=[[int(x)%p for x in row] for row in M]; n=len(M); r=0
    for c in range(n):
        piv=next((i for i in range(r,n) if M[i][c]),None)
        if piv is None: continue
        M[r],M[piv]=M[piv],M[r]; inv=pow(M[r][c],p-2,p)
        M[r]=[x*inv%p for x in M[r]]
        for i in range(n):
            if i!=r and M[i][c]:
                f=M[i][c]; Mi=M[i]; Mr=M[r]; M[i]=[(a-f*b)%p for a,b in zip(Mi,Mr)]
        r+=1
    return n-r
for arg in sys.argv[1:]:
    n,lam=map(int,arg.split(':'))
    G=gram(n); ev=np.linalg.eigvalsh(G)-4
    d=np.sort(np.abs(ev-lam))[:4]
    M=(G-(lam+4)*np.eye(len(G))).astype(np.int64)
    print(n,lam,'closest distances',d,'nullity mod p',nullity_mod(M.tolist(),1000003),flush=True)
