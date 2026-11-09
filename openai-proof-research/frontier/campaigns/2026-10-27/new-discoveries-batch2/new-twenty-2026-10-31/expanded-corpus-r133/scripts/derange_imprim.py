# For G=A_n, H=(S_a wr S_b) ∩ A_n (n=ab, a,b>=2): proportion of elements of A_n lying in some conjugate of H
# (= 1 - delta(G,H)). Element preserves a block system with b blocks of size a iff its cycle multiset splits into
# groups {l*mu_1,...,l*mu_r} with mu a partition of a. Compare with f(n,1) = 1 - delta(A_n, natural).
import sys, math
from fractions import Fraction
from functools import lru_cache
def partitions(n,maxp=None):
    if maxp is None: maxp=n
    if n==0: yield (); return
    for k in range(min(n,maxp),0,-1):
        for rest in partitions(n-k,k): yield (k,)+rest
def classsize_over_fact(lam):
    from collections import Counter
    c=Counter(lam); den=1
    for k,m in c.items(): den*=k**m*math.factorial(m)
    return Fraction(1,den)
def make_good(a):
    pa=list(partitions(a))
    @lru_cache(maxsize=None)
    def good(ms):  # ms sorted tuple descending
        if not ms: return True
        top=ms[0]
        # the group containing the largest part 'top': top = l*mu_1 with mu_1 max of mu
        for l in range(1,top+1):
            if top%l: continue
            for mu in pa:
                if mu[0]*l!=top: continue
                need=[l*x for x in mu]
                rem=list(ms); ok=True
                for x in need:
                    try: rem.remove(x)
                    except ValueError: ok=False; break
                if ok and good(tuple(rem)): return True
        return False
    return good
N=int(sys.argv[1])
for n in range(5,N+1):
    nat_der=Fraction(sum((-1)**j*Fraction(1,math.factorial(j)) for j in range(n+1)))  # delta(S_n)
    f1=1-(nat_der-Fraction((-1)**n*(n-1),math.factorial(n)))
    parts=list(partitions(n))
    worst=None
    for a in range(2,n//2+1):
        if n%a: continue
        b=n//a; good=make_good(a)
        prop=Fraction(0)
        for lam in parts:
            if (n-len(lam))%2: continue
            if good(lam): prop+=classsize_over_fact(lam)
        prop*=2  # proportion within A_n
        r=(float(prop),a,b)
        if worst is None or r>worst: worst=r
    if worst: print(n,'f(n,1)=',float(f1),'max imprimitive fix-proportion',worst,'margin',float(f1)-worst[0],flush=True)
