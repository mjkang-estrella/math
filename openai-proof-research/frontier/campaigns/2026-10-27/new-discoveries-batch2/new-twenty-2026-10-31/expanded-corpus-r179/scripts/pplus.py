# Berczi-Schwarcz arXiv:2302.01445 Conjecture conj:pp (property P+). Reduction: contract A cap B, restrict to A cup B:
# WLOG E = A u B disjoint bases of rank r. Need orderings a_1 b_1 a_2 b_2 ... a_r b_r (path; by reversal WLOG starts in A)
# such that every circuit contains two consecutive path elements. Random vector matroids [I | X] over GF(p), A = first r columns.
import sys, random, itertools, time
r,p,seed,secs=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4]); rnd=random.Random(seed); q0=float(sys.argv[5]) if len(sys.argv)>5 else 0.0
def rank(cols, vecs):
    rows=[list(vecs[c]) for c in cols]; rk=0; m=len(rows[0]) if rows else 0
    for j in range(m):
        piv=None
        for i in range(rk,len(rows)):
            if rows[i][j]%p: piv=i; break
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]; inv=pow(rows[rk][j],p-2,p)
        rows[rk]=[x*inv%p for x in rows[rk]]
        for i in range(len(rows)):
            if i!=rk and rows[i][j]%p:
                f=rows[i][j]; rows[i]=[(x-f*y)%p for x,y in zip(rows[i],rows[rk])]
        rk+=1
    return rk
def circuits(vecs,n):
    C=[]; dep=set()
    for k in range(1,n+1):
        for S in itertools.combinations(range(n),k):
            if any(set(c)<=set(S) for c in C): continue
            if rank(S,vecs)<k: C.append(S)
    return C
t0=time.time(); tested=0; bad=0
while time.time()-t0<secs:
    X=[[0 if rnd.random()<q0 else rnd.randrange(1,p) for _ in range(r)] for _ in range(r)]
    vecs=[tuple(1 if i==j else 0 for i in range(r)) for j in range(r)]+[tuple(X[i][j] for i in range(r)) for j in range(r)]
    if rank(range(r,2*r),vecs)<r: continue   # B must be a basis
    n=2*r; C=circuits(vecs,n)
    if any(len(c)==1 for c in C): continue  # loops impossible here anyway
    masks=[sum(1<<e for e in c) for c in C]
    found=False
    A=list(range(r)); B=list(range(r,2*r))
    for pa in itertools.permutations(A):
        for pb in itertools.permutations(B):
            seq=[x for pair in zip(pa,pb) for x in pair]
            edges=[(1<<seq[i])|(1<<seq[i+1]) for i in range(n-1)]
            if all(any(m&e==e for e in edges) for m in masks): found=True; break
        if found: break
    tested+=1
    if not found:
        bad+=1; print('COUNTEREXAMPLE p',p,'r',r,'X',X,'circuits',C,flush=True); break
print('r',r,'p',p,'seed',seed,'matroids tested',tested,'counterexamples',bad,'time',round(time.time()-t0,1))
