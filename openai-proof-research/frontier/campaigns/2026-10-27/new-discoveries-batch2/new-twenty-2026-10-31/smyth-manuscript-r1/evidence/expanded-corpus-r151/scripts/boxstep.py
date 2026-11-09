# Step lemma test: box prod [0,c_i], N=sum c, for 2k+1<=N, matching L_k -> L_{k+1} saturating L_k,
# where x -> x+e_j allowed iff 2*x_j+1 <= c_j (coordinate j stays no less central).
import itertools,sys
def levels(c):
    L={}
    for x in itertools.product(*[range(ci+1) for ci in c]): L.setdefault(sum(x),[]).append(x)
    return L
def match(U,V,nbr):
    Vi={v:i for i,v in enumerate(V)}; mt=[None]*len(V)
    def aug(u,seen):
        for v in nbr(u):
            j=Vi[v]
            if j in seen: continue
            seen.add(j)
            if mt[j] is None or aug(mt[j],seen): mt[j]=u; return True
        return False
    sys.setrecursionlimit(100000)
    return sum(1 for u in U if aug(u,set()))
def nbr_c(c):
    def f(x):
        for j in range(len(c)):
            if 2*x[j]+1<=c[j]: yield x[:j]+(x[j]+1,)+x[j+1:]
    return f
maxc=int(sys.argv[1]); maxB=int(sys.argv[2]); maxsize=int(sys.argv[3])
bad=0;cnt=0
for B in range(1,maxB+1):
    for c in itertools.combinations_with_replacement(range(1,maxc+1),B):
        size=1
        for ci in c: size*=ci+1
        if size>maxsize: continue
        L=levels(c); N=sum(c)
        for k in range(0,N):
            if 2*k+1>N: break
            m=match(L[k],L[k+1],nbr_c(c)); cnt+=1
            if m<len(L[k]): bad+=1; print('FAIL',c,k,len(L[k]),m,flush=True)
print('cases',cnt,'fail',bad)
