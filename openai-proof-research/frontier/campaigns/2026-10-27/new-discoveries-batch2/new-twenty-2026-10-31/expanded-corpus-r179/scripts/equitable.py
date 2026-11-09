# Equitability (EGRES open problem; Berczi-Schwarcz arXiv:2203.01779 Conj. conj:equitable) on random vector matroids
# [I | X] over GF(p) with E = A u B (A = unit vectors, B = columns of X a basis). For every X subset E need a basis B'
# with E-B' a basis and floor(|X|/2) <= |B' cap X| <= ceil(|X|/2).
import sys, random, itertools, time
r,p,seed,secs,q0=int(sys.argv[1]),int(sys.argv[2]),int(sys.argv[3]),float(sys.argv[4]),float(sys.argv[5]); rnd=random.Random(seed)
def rank(cols, vecs):
    rows=[list(vecs[c]) for c in cols]; rk=0
    for j in range(r):
        piv=next((i for i in range(rk,len(rows)) if rows[i][j]%p),None)
        if piv is None: continue
        rows[rk],rows[piv]=rows[piv],rows[rk]; inv=pow(rows[rk][j],p-2,p); rows[rk]=[x*inv%p for x in rows[rk]]
        for i in range(len(rows)):
            if i!=rk and rows[i][j]%p:
                f=rows[i][j]; rows[i]=[(x-f*y)%p for x,y in zip(rows[i],rows[rk])]
        rk+=1
    return rk
n=2*r; t0=time.time(); tested=0
while time.time()-t0<secs:
    Xm=[[0 if rnd.random()<q0 else rnd.randrange(1,p) for _ in range(r)] for _ in range(r)]
    vecs=[tuple(1 if i==j else 0 for i in range(r)) for j in range(r)]+[tuple(Xm[i][j] for i in range(r)) for j in range(r)]
    if rank(range(r,n),vecs)<r: continue
    pairs=[]
    for S in itertools.combinations(range(n),r):
        m=sum(1<<e for e in S)
        if m&1 and rank(S,vecs)==r and rank([e for e in range(n) if not m>>e&1],vecs)==r: pairs.append(m)
    full=(1<<n)-1; allm=pairs+[full^m for m in pairs]
    ok=True
    for X in range(1<<n):
        k=bin(X).count('1'); lo,hi=k//2,(k+1)//2
        if not any(lo<=bin(m&X).count('1')<=hi for m in allm): ok=False; print('COUNTEREXAMPLE',Xm,X,flush=True); break
    tested+=1
    if not ok: break
print('equitability r',r,'p',p,'q0',q0,'tested',tested,'time',round(time.time()-t0,1))
