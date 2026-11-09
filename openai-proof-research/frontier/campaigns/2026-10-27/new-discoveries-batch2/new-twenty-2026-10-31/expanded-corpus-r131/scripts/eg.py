# Linusson-Potka Conjecture 4.3 checker (arXiv:1804.10034v2, Sec. 4).
# W_Q = {w : EG(w) = Q, P(w) frozen}; P_Q ordered componentwise; c(Q) column word;
# EG^{-1}(Q) the unique reduced word in W_Q (computed via promotion, Thm 2.5, and cross-checked).
import sys, random, json, itertools
def insert(P, x):
    """Edelman-Greene insertion (Definition 2.1), returns (newP, row index of new cell)."""
    P=[r[:] for r in P]; i=0
    while True:
        if i==len(P): P.append([x]); return P,i
        row=P[i]
        if x>row[-1]: row.append(x); return P,i
        if x in row: x=x+1; i+=1; continue
        k=next(t for t,z in enumerate(row) if z>x)
        z=row[k]; row[k]=x; x=z; i+=1
def EG(w):
    P=[]; Q=[]
    for k,x in enumerate(w,1):
        P,i=insert(P,x)
        if i==len(Q): Q.append([])
        Q[i].append(k)
    return P,Q
def frozen(P): return all(P[i][j]==i+j+1 for i in range(len(P)) for j in range(len(P[i])))
def colword(Q,N):
    c=[0]*N
    for i,r in enumerate(Q):
        for j,v in enumerate(r): c[v-1]=j+1
    return tuple(c)
def promotion_inverse(Q,N):
    # Theorem 2.5: repeatedly apply elementary promotion; j_k = column of the largest entry
    T={ (i,j):Q[i][j] for i in range(len(Q)) for j in range(len(Q[i])) }
    js=[]
    for k in range(N):
        live={c:v for c,v in T.items() if v is not None}
        if not live: break
        (i,j)=max(live,key=lambda c:live[c]); js.append(j+1)
        path=[(i,j)]
        while True:
            a,b=path[-1]; cand=[]
            for c in ((a,b-1),(a-1,b)):
                if c in T and T[c] is not None: cand.append((T[c],c))
            if not cand: break
            path.append(max(cand)[1])
        for t in range(len(path)-1): T[path[t]]=T[path[t+1]]
        T[path[-1]]=None
    return tuple(reversed(js))
def W_Q(Q,N,n):
    """All words w over [n-1] with EG(w)=Q and P(w) frozen, via prefix-constrained DFS."""
    rowof={}
    for i,r in enumerate(Q):
        for v in r: rowof[v]=i
    out=[]
    def rec(P,w):
        k=len(w)
        if k==N:
            if frozen(P): out.append(tuple(w))
            return
        for x in range(1,n):
            P2,i=insert(P,x)
            if i==rowof[k+1]: rec(P2,w+[x])
    rec([],[]); return out
def longest_chain(elems,lo,hi):
    S=[e for e in elems if all(a<=b for a,b in zip(lo,e)) and all(a<=b for a,b in zip(e,hi))]
    S.sort(key=sum); L={}
    for e in S:
        best=0 if e==lo else None
        for f in S:
            if f in L and L[f] is not None and f!=e and all(a<=b for a,b in zip(f,e)):
                if best is None or L[f]+1>best: best=L[f]+1
        L[e]=best
    return L.get(hi)
def check(Q,N,n):
    u=promotion_inverse(Q,N); c=colword(Q,N)
    W=W_Q(Q,N,n); Ws=set(W)
    assert u in Ws, ('EG^-1 not in W_Q',Q,u)
    P,QQ=EG(u); assert QQ==Q and frozen(P)
    assert c in Ws and all(all(a<=b for a,b in zip(c,w)) for w in W), 'c(Q) not unique min'
    maximal=not any(w!=u and all(a<=b for a,b in zip(u,w)) for w in W)
    lq=longest_chain(W,c,u); s=sum(a-b for a,b in zip(u,c))
    return dict(maximal=maximal,ell=lq,sum=s,size=len(W))
def all_syt_staircase(n):
    shape=list(range(n-1,0,-1)); N=sum(shape)
    # generate SYT by placing 1..N
    res=[]
    def rec(rows,k):
        if k>N: res.append([r[:] for r in rows]); return
        for i in range(len(shape)):
            if len(rows[i])<shape[i] and (i==0 or len(rows[i-1])>len(rows[i])):
                rows[i].append(k); rec(rows,k+1); rows[i].pop()
    rec([[] for _ in shape],1); return res
def random_syt(n,rng):
    # hook walk (Greene-Nijenhuis-Wilf) on staircase shape: fill N..1
    shape=list(range(n-1,0,-1)); N=sum(shape); cur=shape[:]; T=[[0]*s for s in shape]
    for k in range(N,0,-1):
        cells=[(i,j) for i in range(len(cur)) for j in range(cur[i])]
        i,j=rng.choice(cells)
        while True:
            arm=cur[i]-j-1; leg=sum(1 for r in range(i+1,len(cur)) if cur[r]>j)
            if arm+leg==0: break
            t=rng.randrange(arm+leg)
            if t<arm: j=j+1+t
            else: i=i+1+(t-arm)
        T[i][j]=k; cur[i]-=1
    return T
if __name__=='__main__':
    n=int(sys.argv[1]); mode=sys.argv[2]; N=n*(n-1)//2
    if mode=='all':
        hist={}; bad=[]; sizes=[]
        for Q in all_syt_staircase(n):
            r=check(Q,N,n); hist[r['ell']]=hist.get(r['ell'],0)+1; sizes.append(r['size'])
            if not r['maximal'] or r['ell']!=r['sum']: bad.append((Q,r))
        print('n',n,'tableaux',len(sizes),'eta',sorted(hist.items()),'maxsize',max(sizes),'failures',len(bad)); print(bad[:3])
    else:
        seed=int(sys.argv[3]); cnt=int(sys.argv[4]); rng=random.Random(seed); bad=[]; done=0; mx=0
        import time; t0=time.time()
        for _ in range(cnt):
            Q=random_syt(n,rng); r=check(Q,N,n); done+=1; mx=max(mx,r['size'])
            if not r['maximal'] or r['ell']!=r['sum']: bad.append((Q,r)); print('FAIL',Q,r,flush=True)
            if time.time()-t0>100: break
        print('n',n,'seed',seed,'sampled',done,'max |W_Q|',mx,'failures',len(bad),flush=True)
