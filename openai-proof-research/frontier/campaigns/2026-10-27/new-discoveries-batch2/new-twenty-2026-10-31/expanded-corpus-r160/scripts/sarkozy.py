# Cayley graph on F_p^{d} (p prime) of differences that are k-th powers of polynomials b with deg b <= e,
# restricted to coefficient vectors of degree < n. Vertices: all polys deg < n (as tuples). For speed we restrict
# to the subspace spanned by the k-th powers when requested.
import sys, itertools, random, time
def polymul(a,b,p):
    r=[0]*(len(a)+len(b)-1)
    for i,x in enumerate(a):
        if x:
            for j,y in enumerate(b): r[i+j]=(r[i+j]+x*y)%p
    return r
def kth_powers(p,k,n):
    e=(n-1)//k
    S=set()
    for b in itertools.product(range(p),repeat=e+1):
        if not any(b): continue
        r=[1]
        for _ in range(k): r=polymul(r,list(b),p)
        r=(r+[0]*n)[:n] if len(r)<=n else None
        if r is None or len(r)!=n: continue
        S.add(tuple(r))
    return S
def build(p,k,n):
    S=kth_powers(p,k,n)
    D=set(S)|{tuple((-x)%p for x in s) for s in S}
    used=[i for i in range(n) if any(s[i] for s in D)]
    d=len(used)
    Dr=[tuple(s[i] for i in used) for s in D]
    verts=list(itertools.product(range(p),repeat=d))
    idx={v:i for i,v in enumerate(verts)}
    adj=[0]*len(verts)
    for i,v in enumerate(verts):
        m=0
        for s in Dr:
            w=tuple((a+b)%p for a,b in zip(v,s)); m|=1<<idx[w]
        adj[i]=m
    return verts,adj,used,Dr
def greedy_ls(adj,N,iters,seed):
    rnd=random.Random(seed); best=0; bestset=None
    for it in range(iters):
        order=list(range(N)); rnd.shuffle(order)
        A=0
        for v in order:
            if not adj[v]&A: A|=1<<v
        # simple (1,2)-swap local search
        improved=True
        while improved:
            improved=False
            Aset=[v for v in range(N) if A>>v&1]
            free=[v for v in range(N) if not A>>v&1 and bin(adj[v]&A).count('1')==1]
            rnd.shuffle(free)
            for v in free:
                u=(adj[v]&A).bit_length()-1
                B=A&~(1<<u)|(1<<v)
                # find w not in B with no neighbours in B
                cand=[w for w in range(N) if not B>>w&1 and not adj[w]&B and w!=u]
                if cand:
                    B|=1<<cand[0]
                    for w in cand[1:]:
                        if not adj[w]&B and not B>>w&1: B|=1<<w
                    A=B; improved=True; break
        c=bin(A).count('1')
        if c>best: best=c; bestset=A
    return best,bestset
if __name__=='__main__':
    p,k,n=map(int,sys.argv[1:4]); iters=int(sys.argv[4])
    t=time.time()
    verts,adj,used,Dr=build(p,k,n)
    N=len(verts); deg=bin(adj[0]).count('1')
    print('p,k,n',p,k,n,'used coords',used,'N',N,'deg',deg,'bound for full space q^(n(1-1/k^2))',p**(n*(1-1/k**2)),'per-subspace target >',p**(n*(1-1/k**2))/p**(n-len(used)))
    b,A=greedy_ls(adj,N,iters,1)
    print('local search best',b,'x',p**(n-len(used)),'=',b*p**(n-len(used)),'sec',round(time.time()-t,1))
