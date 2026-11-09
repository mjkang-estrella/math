import numpy as np, itertools, random, sys, json
def legendre(a,p):
    a%=p
    if a==0: return 0
    return 1 if pow(a,(p-1)//2,p)==1 else -1
def paley(p):
    n=p+1; W=np.zeros((n,n),dtype=np.int64)
    eps = 1 if p%4==1 else -1
    W[0,1:]=1; W[1:,0]=eps
    for i in range(p):
        for j in range(p): W[i+1,j+1]=legendre(j-i,p)
    return W
def circ(r):
    m=len(r); return np.array([[r[(j-i)%m] for j in range(m)] for i in range(m)],dtype=np.int64)
def paf(r,s): m=len(r); return sum(r[i]*r[(i+s)%m] for i in range(m))
def gs_skew(m, limit=None):
    """Goethals-Seidel skew-Hadamard of order 4m; yield W=H-I conference matrices."""
    seqs=list(itertools.product([1,-1],repeat=m))
    As=[a for a in seqs if a[0]==1 and all(a[(m-i)%m]==-a[i] for i in range(1,m))]
    pafs={s:[paf(s,t) for t in range(1,m)] for s in seqs}
    R=np.array([[1 if i+j==m-1 else 0 for j in range(m)] for i in range(m)],dtype=np.int64)
    out=[]
    for a in As:
        for b in seqs:
            for c in seqs:
                need=[-(pafs[a][t]+pafs[b][t]+pafs[c][t]) for t in range(m-1)]
                for d in seqs:
                    if pafs[d]==need:
                        A,B,C,D=map(circ,(a,b,c,d))
                        H=np.block([[A,B@R,C@R,D@R],[-B@R,A,D.T@R,-C.T@R],[-C@R,-D.T@R,A,B.T@R],[-D@R,C.T@R,-B.T@R,A]])
                        n=4*m
                        assert (H@H.T==n*np.eye(n,dtype=np.int64)).all()
                        W=H-np.eye(n,dtype=np.int64)
                        assert (W.T==-W).all()
                        out.append(((a,b,c,d),W))
                        if limit and len(out)>=limit: return out
    return out
def is_conference(W):
    n=W.shape[0]
    return (np.diag(W)==0).all() and set(np.unique(W[~np.eye(n,dtype=bool)]))<= {1,-1} and (W@W.T==(n-1)*np.eye(n,dtype=np.int64)).all()
def rref_mod(M,p):
    M=M.copy()%p; r=0; piv=[]
    rows,cols=M.shape
    for c in range(cols):
        pr=None
        for i in range(r,rows):
            if M[i,c]%p: pr=i;break
        if pr is None: continue
        M[[r,pr]]=M[[pr,r]]
        inv=pow(int(M[r,c]),p-2,p); M[r]=(M[r]*inv)%p
        for i in range(rows):
            if i!=r and M[i,c]: M[i]=(M[i]-M[i,c]*M[r])%p
        piv.append(c); r+=1
        if r==rows: break
    return M[:r],piv
def low_weight_search(G,p,k,trials=20000,seed=1):
    """G: kxn generator in rref. Find nonzero codeword with >=k zeros: choose k-1 zero positions, solve."""
    rng=random.Random(seed); n=G.shape[1]
    best=None
    for t in range(trials):
        S=rng.sample(range(n),k-1)
        # find c (len k) with c^T G[:,S]=0 : null space of G[:,S]^T (k-1 eqs, k unknowns)
        Msub=G[:,S].T  # (k-1) x k
        R,piv=rref_mod(Msub,p)
        free=[j for j in range(k) if j not in piv]
        c=np.zeros(k,dtype=np.int64); c[free[0]]=1
        for i,pc in enumerate(piv): c[pc]=(-R[i,free[0]])%p
        w=(c@G)%p; wt=int((w!=0).sum())
        if best is None or wt<best[0]: best=(wt,c.copy(),w.copy())
        if wt<n-k+1: return best
    return best
