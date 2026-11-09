# Uniform construction for prime q = 1 mod 4: X = {v : 4xz - y^2 = c} (c nonsquare) u {t*(a^2,2ab,b^2) : [a:b] in PG(1,q), t in I},
# I = greedy set of nonzero squares with no two differing by a nonzero square. Verify independence directly against
# all squares of polynomials b0 + b1 T (coefficient vectors (b0^2, 2 b0 b1, b1^2)); report |X| vs q^2.
import sys,itertools
for p in [int(x) for x in sys.argv[1].split(',')]:
    assert p%4==1
    sq={(x*x)%p for x in range(1,p)}; c=min(x for x in range(1,p) if x not in sq)
    I=[]
    for t in sorted(sq):
        if all(((t-u)%p) not in sq for u in I): I.append(t)
    reps=[(1,b) for b in range(p)]+[(0,1)]
    X=set(v for v in itertools.product(range(p),repeat=3) if (4*v[0]*v[2]-v[1]*v[1])%p==c)
    nL=len(X)
    for (a,b) in reps:
        for t in I: X.add(((t*a*a)%p,(2*t*a*b)%p,(t*b*b)%p))
    P=set()
    for b0 in range(p):
        for b1 in range(p):
            if b0 or b1: P.add(((b0*b0)%p,(2*b0*b1)%p,(b1*b1)%p))
    Xl=list(X); bad=sum(1 for u in Xl for v in Xl if u!=v and tuple((x-y)%p for x,y in zip(u,v)) in P)
    print('q',p,'c',c,'I',I,'|L|',nL,'|X|',len(X),'formula q^2-q+(q+1)|I|',p*p-p+(p+1)*len(I),'q^2',p*p,'violations',bad)
