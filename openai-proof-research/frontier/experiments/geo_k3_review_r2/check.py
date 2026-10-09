"""Independent exact checks; run python3 -I check.py. No scout code imported.

Hilbert signs are compared with a quaternion decomposition of the full Clifford
algebra. Positive embeddings have explicit complementary forms. A failed bounded
search is never used to prove nonembedding.
"""
from fractions import Fraction as F
from itertools import combinations, product
from math import prod
import random


def factors(n):
    n = abs(n)
    ans = set()
    p = 2
    while p*p <= n:
        while n % p == 0:
            ans.add(p)
            n //= p
        p += 1
    if n > 1:
        ans.add(n)
    return ans


def squareclass(x):
    x = F(x)
    n = x.numerator*x.denominator
    ans = -1 if n < 0 else 1
    for p in factors(n):
        v = 0
        while n % p == 0:
            n //= p
            v += 1
        if v % 2:
            ans *= p
    return ans


def places(q):
    return sorted({2}.union(*(factors(squareclass(a)) for a in q))) + ['R']


def unit(x, p):
    x = squareclass(x)
    if x % p == 0:
        return 1, x//p
    return 0, x


def h(a, b, p):
    if p == 'R':
        return -1 if a < 0 and b < 0 else 1
    r, u = unit(a, p)
    s, v = unit(b, p)
    if p == 2:
        parity = (u-1)*(v-1)//4 + r*(v*v-1)//8 + s*(u*u-1)//8
        return (-1)**(parity % 2)
    sign = (-1)**(r*s*((p-1)//2))
    for z, power in [(u,s),(v,r)]:
        if power and pow(z % p,(p-1)//2,p) != 1:
            sign = -sign
    return sign


def hasse(q,p):
    return prod(h(a,b,p) for a,b in combinations(q,2))


def square_at(a,p):
    a = squareclass(a)
    if p == 'R':
        return a > 0
    r,u = unit(a,p)
    return r == 0 and (u % 8 == 1 if p == 2 else pow(u % p,(p-1)//2,p) == 1)


VP = [1,-1,1,-1,-1,-1,-1,-1]


def signature(q):
    return (sum(x > 0 for x in q),sum(x < 0 for x in q))


def isometric(q,r):
    return (len(q) == len(r) and signature(q) == signature(r)
            and squareclass(prod(q)*prod(r)) == 1
            and all(hasse(q,p) == hasse(r,p) for p in places(q+r)))


def full_clifford(q,p):
    a,b,c,d,e,f = q
    # C(q) = (a,b) tensor (-ab*c,-ab*d) tensor (abcd*e,abcd*f).
    return h(a,b,p)*h(-a*b*c,-a*b*d,p)*h(a*b*c*d*e,a*b*c*d*f,p)


def classify(q):
    delta = squareclass(prod(q))
    bad_p = [p for p in places(q) if p != 'R' and square_at(-delta,p)
             and hasse(q,p) == -1]
    bad_w = [p for p in places(q) if p != 'R' and square_at(-delta,p)
             and full_clifford(q,p) == -1]
    return delta,bad_p,bad_w


def witnesses(q):
    delta,bp,bw = classify(q)
    N = None
    wm = None
    if not bp:
        for a in range(1,10001):
            candidate = [-a,-a*delta]
            if isometric(q+candidate,VP):
                N = candidate
                break
        assert N is not None, ('positive search inconclusive',q)
    if not bw:
        for m in range(1,20001):
            if isometric(q+[m*delta],[1,-1,1,-1,1,-1,-m]):
                wm = m
                break
        assert wm is not None, ('positive search inconclusive',q)
    return N,wm


def diagonalize(G):
    G = [[F(x) for x in row] for row in G]
    out = []
    while G:
        n = len(G)
        if G[0][0] == 0:
            k = next((i for i in range(n) if G[i][i]),None)
            if k is not None:
                G[0],G[k] = G[k],G[0]
                for row in G:
                    row[0],row[k] = row[k],row[0]
            else:
                k = next(i for i in range(1,n) if G[0][i])
                for j in range(n):
                    G[0][j] += G[k][j]
                for i in range(n):
                    G[i][0] += G[i][k]
        a = G[0][0]
        assert a
        out.append(a)
        G = [[G[i][j]-G[i][0]*G[0][j]/a for j in range(1,n)] for i in range(1,n)]
    return out


def cubic_trace_gram(coeff):
    # F=Q(t), t^3+t^2-2t-1=0. Newton sums followed by recurrence.
    traces = [3,-1,5]
    for k in range(3,10):
        traces.append(-traces[k-1]+2*traces[k-2]+traces[k-3])
    return [[2*sum(c*traces[k+i+j] for k,c in enumerate(coeff))
             for j in range(3)] for i in range(3)]


if __name__ == '__main__':
    random.seed(20261008)
    pool = [1,2,3,5,7,10,11,13,17,19]
    for _ in range(1000):
        q = random.choices(pool,k=2)+[-x for x in random.choices(pool,k=4)]
        for p in places(q):
            assert full_clifford(q,p) == hasse(q,p)*h(-1,-1,p)
        assert prod(hasse(q,p) for p in places(q)) == 1
        d,bp,bw = classify(q)
        oddbad = [p for p in bp if p != 2]
        assert (not bp or not bw) == (not oddbad)
    print('1000 exact full-Clifford/Hasse and union checks passed')
    examples = [
        [21,2,-6,-19,-2,-10],
        [3,2,-13,-10,-3,-15],
        [19,13,-21,-14,-14,-21],
        [14,1,-21,-5,-7,-14],
    ]
    for q in examples:
        d,bp,bw = classify(q)
        print('\nq=',q,'det squareclass=',d,'2 splits=',square_at(-d,2))
        print('local data (place,Hasse,full Clifford,K splits):',
              [(p,hasse(q,p),full_clifford(q,p),square_at(-d,p)) for p in places(q)])
        print('VP obstructions=',bp,'W obstructions=',bw,'complement/W_m witness=',witnesses(q))
    # E=F(sqrt(-beta)), alpha=t, beta totally positive.
    # q=Tr_E(alpha*x*bar(y)) = 2Tr_F(alpha*u*u'+alpha*beta*v*v').
    # Put h20 at one embedding above the positive embedding of alpha. The
    # rational (1,1) subspace is E-stable, hence zero in this rank-one E-module;
    # polarizable K3 type then implies simplicity (see the review).
    for a,b,c in product(range(-3,5),repeat=3):
        if (a,b,c) == (0,0,0):
            continue
        if signature(diagonalize(cubic_trace_gram([a,b,c]))) != (3,0):
            continue
        A = cubic_trace_gram([0,1])
        B = cubic_trace_gram([0,a,b,c])
        G = [row+[0]*3 for row in A]+[[0]*3+row for row in B]
        q = diagonalize(G)
        assert signature(q) == (2,4)
        d,bp,bw = classify(q)
        if bp and bw:
            print('\nCM COUNTEREXAMPLE alpha=t, beta coefficients=',(a,b,c))
            print('Gram=',G)
            print('exact diagonal=',list(map(str,q)))
            print('diagonal squareclasses=',list(map(squareclass,q)))
            print('det squareclass=',d,'VP obstructions=',bp,'W obstructions=',bw)
            print('bad odd local data=',[(p,hasse(q,p),square_at(-d,p)) for p in bp if p != 2])
            break
    else:
        raise AssertionError('no CM example found')
