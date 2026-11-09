# Probe Elphick-Linz-Wocjan: Lambda_l(G) <= 2(1-1/omega), l=min(n+,omega).
import numpy as np, itertools, sys, random
def clique_number(adj,n):
    best=0
    def ext(R,P):
        nonlocal best
        if not P:
            best=max(best,len(R)); return
        if len(R)+len(P)<=best: return
        for v in list(P):
            ext(R|{v}, P & adj[v]); P=P-{v}
            if len(R)+len(P)<=best: return
    ext(set(),set(range(n))); return best
def score(A):
    n=A.shape[0]; m=A.sum()/2
    if m==0: return None
    ev=np.sort(np.linalg.eigvalsh(A))[::-1]
    npos=int((ev>1e-9).sum())
    adj=[set(np.nonzero(A[i])[0]) for i in range(n)]
    w=clique_number(adj,n); l=min(npos,w)
    s=(ev[:l]**2).sum()
    return s/m-2*(1-1/w), w, npos, m
rnd=random.Random(int(sys.argv[1]) if len(sys.argv)>1 else 0)
best=(-9,None)
for w in range(2,6):
    t=w
    n=w*t
    base=np.zeros((n,n),int)
    for b in range(t):
        for i in range(b*w,(b+1)*w):
            for j in range(b*w,(b+1)*w):
                if i!=j: base[i,j]=1
    for trial in range(300):
        A=base.copy()
        k=rnd.randint(1,6)
        for _ in range(k):
            i,j=rnd.sample(range(n),2)
            if i//w!=j//w: A[i,j]=A[j,i]=1
        r=score(A)
        if r and r[0]>best[0]: best=(r[0],(w,r))
        if r and r[0]>1e-9: print('VIOL',w,r,np.argwhere(np.triu(A-base)).tolist()); break
print('best',best)
