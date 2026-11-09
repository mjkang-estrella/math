# Exact joint distribution of (inv~, fmaj) over G_{c,n} per Arslan-Ahmia-Alemdar arXiv:2512.02404 eqs (2),(3),(6).
import sys, itertools
from collections import Counter
def stats(perm,cols,c):
    n=len(perm)
    inv=sum(1 for i in range(n) for j in range(i+1,n) if perm[i]>perm[j])
    col=sum(cols)
    key=[((c-t) if t else c, v) for v,t in zip(perm,cols)]
    maj=sum(i+1 for i in range(n-1) if key[i]>key[i+1])
    return c*inv+col, c*maj+col
def check(c,n):
    D=Counter()
    for p in itertools.permutations(range(1,n+1)):
        for cols in itertools.product(range(c),repeat=n):
            D[stats(p,cols,c)]+=1
    asym=[(k,D[k],D[(k[1],k[0])]) for k in D if D[k]!=D[(k[1],k[0])]]
    return D,asym
# sanity: reproduce Table 2 entries for G_{3,2}
assert stats((2,1),(1,0),3)==(4,1) and stats((1,2),(1,1),3)==(2,2) and stats((1,2),(2,1),3)==(3,3)
for c,n in [(3,2),(4,2),(3,3),(4,3),(2,3),(2,4),(3,4),(2,5),(4,4),(5,3),(2,6)]:
    D,asym=check(c,n)
    print(c,n,'size',sum(D.values()),'asymmetric pairs',len(asym), sorted(asym)[:4],flush=True)
