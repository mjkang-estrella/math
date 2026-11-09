# Independent from-scratch verification (pure Python ints). Usage: python3 -I verify_from_scratch.py <cex20_certificate.json> <out.json>
import json, sys, itertools
p=19; n=20; k=10
W=json.load(open(sys.argv[1]))['W']
# 1. source conference-matrix definition: entries in {0,1,-1}, each row/col exactly n-1 nonzeros, W W^T = (n-1) I
assert len(W)==n and all(len(r)==n for r in W)
assert all(x in (0,1,-1) for r in W for x in r)
assert all(sum(1 for x in r if x)==n-1 for r in W)
assert all(sum(1 for i in range(n) if W[i][j])==n-1 for j in range(n))
G=[[sum(W[i][t]*W[j][t] for t in range(n)) for j in range(n)] for i in range(n)]
assert all(G[i][j]==((n-1) if i==j else 0) for i in range(n) for j in range(n))
skew=all(W[i][j]==-W[j][i] for i in range(n) for j in range(n))
zerodiag=all(W[i][i]==0 for i in range(n))
def rref(M):
    M=[[x%p for x in r] for r in M]; r=0; piv=[]
    for c in range(len(M[0])):
        pr=next((i for i in range(r,len(M)) if M[i][c]),None)
        if pr is None: continue
        M[r],M[pr]=M[pr],M[r]; iv=pow(M[r][c],p-2,p); M[r]=[x*iv%p for x in M[r]]
        for i in range(len(M)):
            if i!=r and M[i][c]:
                f=M[i][c]; M[i]=[(x-f*y)%p for x,y in zip(M[i],M[r])]
        piv.append(c); r+=1
        if r==len(M): break
    return M[:r],piv
B,piv=rref(W); rank=len(B); assert rank==k
# 2. exact minimum distance: every nonzero codeword of weight <=10 vanishes on some 10-set S of columns;
# enumerate all C(20,10) S, compute left kernel of B restricted to S.
def leftker(S):
    # solve c^T B_S = 0, c in F^k : rows of B_S^T are equations
    M=[[B[i][s] for i in range(k)] for s in S]
    R,pv=rref(M); free=[j for j in range(k) if j not in pv]
    basis=[]
    for f in free:
        c=[0]*k; c[f]=1
        for i,pc in enumerate(pv): c[pc]=(-R[i][f])%p
        basis.append(c)
    return basis
def word(c): return [sum(c[i]*B[i][j] for i in range(k))%p for j in range(n)]
best=None; dep=0; hist={}; maxker=0
for S in itertools.combinations(range(n),k):
    K=leftker(S)
    if not K: continue
    dep+=1; maxker=max(maxker,len(K))
    cands=[K[0]] if len(K)==1 else [ [sum(a[t]*K[t][i] for t in range(len(K)))%p for i in range(k)] for a in itertools.product(range(p),repeat=len(K)) if any(a)]
    for c in cands:
        w=word(c); wt=sum(1 for x in w if x)
        if best is None or wt<best[0]: best=(wt,c,w)
print('conference ok; skew',skew,'zerodiag',zerodiag,'rank',rank,'dependent 10-sets',dep,'max kernel dim',maxker,'min weight',best[0])
json.dump({'skew':skew,'zero_diagonal':zerodiag,'rank_F19':rank,'dependent_10_sets':dep,'max_kernel_dim':maxker,'min_distance':best[0] if best else None,'min_word':best[2],'rref_basis':B,'pivots':piv},open(sys.argv[2],'w'))
