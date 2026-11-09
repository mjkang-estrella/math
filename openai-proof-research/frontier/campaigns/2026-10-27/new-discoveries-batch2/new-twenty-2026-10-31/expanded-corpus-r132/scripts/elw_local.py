# Hill-climb/annealing search for violations of ELW: s_l/m - 2(1-1/w) > 0
import numpy as np, sys, random, math
sys.setrecursionlimit(10000)
def clique_number(A):
    n=A.shape[0]; adj=[frozenset(np.nonzero(A[i])[0].tolist()) for i in range(n)]
    best=[0]
    def ext(r,P):
        if not P:
            best[0]=max(best[0],r); return
        if r+len(P)<=best[0]: return
        P=set(P)
        while P:
            if r+len(P)<=best[0]: return
            v=P.pop(); ext(r+1,P & adj[v])
    ext(0,set(range(n))); return best[0]
def f(A):
    m=A.sum()/2
    if m==0: return -9,0,0
    ev=np.sort(np.linalg.eigvalsh(A))[::-1]
    npos=int((ev>1e-9).sum()); w=clique_number(A); l=min(npos,w)
    return (ev[:l]**2).sum()/m-2*(1-1/w), w, npos
seed=int(sys.argv[1]); n=int(sys.argv[2]); W=int(sys.argv[3]); iters=int(sys.argv[4])
rnd=random.Random(seed)
bestall=-9
for rep in range(1000):
    A=np.zeros((n,n),int)
    for i in range(n):
        for j in range(i+1,n):
            if rnd.random()<0.5: A[i,j]=A[j,i]=1
    cur,w,npos=f(A)
    # penalize w>W
    def g(A):
        v,w,npos=f(A)
        return (v if w<=W else v-1.0*(w-W)), w, npos
    cur,w,npos=g(A); T=0.02
    for it in range(iters):
        i,j=rnd.sample(range(n),2)
        A[i,j]^=1;A[j,i]^=1
        new,w2,np2=g(A)
        if new>=cur or rnd.random()<math.exp((new-cur)/T): cur=new
        else: A[i,j]^=1;A[j,i]^=1
        T*=0.999
    v,w,npos=f(A)
    if v>bestall:
        bestall=v; print(rep,'best',v,w,npos,flush=True)
        if v>1e-9: print('VIOLATION',np.argwhere(np.triu(A)).tolist(),flush=True)
