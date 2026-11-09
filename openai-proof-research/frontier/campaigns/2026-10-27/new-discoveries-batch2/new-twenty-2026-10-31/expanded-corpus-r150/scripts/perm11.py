# Small-graph check of Conjecture 1 in arXiv:1705.08150: every graph has a permanent-non-singular (1,1)-matrix.
# Equivalent: prod_{e=(u,v)} (sum_z A[e,z] x_z) has a squarefree monomial with nonzero coefficient.
# Method: random column subsets + Ryser permanent; fallback exact multilinear DP modulo two primes.
import sys, itertools, random, time
nmax=int(sys.argv[1]); random.seed(1)
def graphs(n):
    pairs=list(itertools.combinations(range(n),2)); seen=set()
    perms=list(itertools.permutations(range(n)))
    for mask in range(1<<len(pairs)):
        E=[pairs[i] for i in range(len(pairs)) if mask>>i&1]
        key=min(tuple(sorted(tuple(sorted((p[a],p[b]))) for a,b in E)) for p in perms) if n<=6 else None
        if key in seen: continue
        seen.add(key); yield E
def matrix(n,E):
    cols=n+len(E); A=[]
    for i,(u,v) in enumerate(E):
        row=[0]*cols; row[v]=1; row[u]=-1
        for k,(a,b) in enumerate(E):
            if k==i: continue
            if v in (a,b): row[n+k]+=1
            if u in (a,b): row[n+k]-=1
        A.append(row)
    return A
def ryser(M):
    m=len(M); tot=0
    for S in range(1,1<<m):
        prod=1
        for r in M:
            s=0
            for j in range(m):
                if S>>j&1: s+=r[j]
            prod*=s
            if prod==0: break
        tot+=(-1)**bin(S).count('1')*prod
    return (-1)**m*tot
def exact_nonzero(A,p):
    cols=len(A[0]); cur={0:1}
    for r in A:
        nz=[(j,c) for j,c in enumerate(r) if c]
        nxt={}
        for mono,coef in cur.items():
            for j,c in nz:
                if mono>>j&1: continue
                k=mono|1<<j; nxt[k]=(nxt.get(k,0)+coef*c)%p
        cur={k:v for k,v in nxt.items() if v}
    return len(cur)>0
t0=time.monotonic(); stats={}
for n in range(1,nmax+1):
    cnt=0; viaexact=0
    for E in graphs(n):
        m=len(E)
        if m==0: cnt+=1; continue
        A=matrix(n,E); cols=n+m; found=False
        for trial in range(30):
            Z=sorted(random.sample(range(cols),m))
            if ryser([[r[j] for j in Z] for r in A])!=0: found=True; break
        if not found:
            viaexact+=1
            found=exact_nonzero(A,1000003) or exact_nonzero(A,998244353)
        if not found: print('COUNTEREXAMPLE',n,E,flush=True)
        cnt+=1
    print('n',n,'graphs',cnt,'exact_fallbacks',viaexact,'secs',round(time.monotonic()-t0,1),flush=True)
