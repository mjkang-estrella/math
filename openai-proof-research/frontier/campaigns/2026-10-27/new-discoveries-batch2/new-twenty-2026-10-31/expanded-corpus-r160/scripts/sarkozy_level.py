# For q=p prime = 1 mod 4: L = D^{-1}(c) (c nonsquare), D(x,y,z)=4xz-y^2. Check L independent in Cay(F_p^3, S);
# Z = cone points (D=0, incl. 0) with no S-neighbour in L; alpha(Z) by exact/ILS; total |L|+alpha(Z) vs p^2.
import sys,os,itertools,time
sys.path.insert(0,os.path.dirname(os.path.abspath(__file__)))
from ils import ils
p=int(sys.argv[1]); secs=float(sys.argv[2])
sq={(x*x)%p for x in range(1,p)}; c=min(x for x in range(1,p) if x not in sq)
S=set()
for a in range(p):
    for b in range(p):
        if a or b:
            s=((a*a)%p,(2*a*b)%p,(b*b)%p); S.add(s); S.add(tuple((-t)%p for t in s))
D=lambda v:(4*v[0]*v[2]-v[1]*v[1])%p
pts=list(itertools.product(range(p),repeat=3))
L=[v for v in pts if D(v)==c]; Ls=set(L)
indepL=not any(tuple((a+b)%p for a,b in zip(v,s)) in Ls for v in L for s in S)
cone=[v for v in pts if D(v)==0]
Z=[v for v in cone if not any(tuple((a+b)%p for a,b in zip(v,s)) in Ls for s in S)]
idx={v:i for i,v in enumerate(Z)}; N=len(Z); adj=[0]*N
for i,v in enumerate(Z):
    for s in S:
        j=idx.get(tuple((a+b)%p for a,b in zip(v,s)))
        if j is not None: adj[i]|=1<<j
best,it=ils(adj,N,secs,1) if N else (set(),0)
print('p',p,'c',c,'|L|',len(L),'L independent',indepL,'|Z| (compatible cone pts)',N,'alpha(Z)>=',len(best),'total',len(L)+len(best),'p^2',p*p,'excess',len(L)+len(best)-p*p,flush=True)
