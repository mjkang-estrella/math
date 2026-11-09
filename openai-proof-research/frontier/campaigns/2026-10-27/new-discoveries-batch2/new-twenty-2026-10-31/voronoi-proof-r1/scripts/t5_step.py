# One-coordinate step identity test.  For profile m and a move of one coordinate in class g:
#   sigma(e_j) - 1/8 = (1/2) E[ Sh(X+1_{gperp}) + Sh(X-1_{gperp}) - Sh(X+1_{g1}) - Sh(X-1_{g1}) ],
# X_a = sum_{f(a)=1} e_f over the reduced profile m' = m - e_g (e_f = signed agreement with player 0).
# Here we (i) verify the identity exactly against the convolution checker, (ii) test whether the
# integrand Phi0(e) is <= 0 pointwise, after translation-symmetrisation, and after sign-class averaging,
# for e in a box with the parity of m'.
import sys; sys.path.insert(0, 'scripts')
from vk import *
import itertools
from math import comb
CH = [[1 - 2 * fval(f, a) for f in range(1, 8)] for a in range(8)]
def Sh(z):
    if min(z) < 0: return Fraction(0)
    return Fraction(1, 1 + sum(1 for q in z if q == 0))
def phi0(e, g):
    X = [sum(e[f - 1] for f in range(1, 8) if fval(f, a)) for a in range(1, 8)]
    gp = [1 if fval(g, a) == 0 else 0 for a in range(1, 8)]
    g1 = [1 - q for q in gp]
    return (Sh([x + q for x, q in zip(X, gp)]) + Sh([x - q for x, q in zip(X, gp)])
            - Sh([x + q for x, q in zip(X, g1)]) - Sh([x - q for x, q in zip(X, g1)]))
def phisym(e, g):  # average over the 8 character sign flips (translations), exact law-preserving
    return sum(phi0([e[f - 1] * CH[b][f - 1] for f in range(1, 8)], g) for b in range(8)) / 8
def exact_step(m, g):  # E[phi0]/2 by exact enumeration over e
    mp = list(m); mp[g - 1] -= 1
    tot = Fraction(0); W = 0
    ranges = [range(-k, k + 1, 2) for k in mp]
    for e in itertools.product(*ranges):
        w = 1
        for k, x in zip(mp, e): w *= comb(k, (k + x) // 2)
        tot += w * phi0(e, g); W += w
    return tot / W / 2
# (i) identity check
for m in [(2,1,1,1,1,1,1), (1,1,1,1,1,1,1), (3,2,2,2,2,2,2), (2,2,2,2,2,2,2)]:
    n = sum(m); P = positions(m); S = scores_all(n, P[1:])
    off = 0
    for g in range(1, 8):
        v = 1 << off; off += m[g - 1]
        lhs = frac(S[v], n) - Fraction(1, 8)
        rhs = exact_step(m, g)
        assert lhs == rhs, (m, g, lhs, rhs)
    print('step identity verified for', m)
# (ii) pointwise / symmetrised / sign-class tests
K = int(sys.argv[1])
for name, mpar, gs in [('t even, g=f1: m\' uniform even', (0,)*7, [1]),
                       ('t even, g=f2', (1,1,0,0,0,0,0), [2]),
                       ('t odd, g=f1: m\' all odd', (1,)*7, [1]),
                       ('t odd, g=f2', (0,0,1,1,1,1,1), [2]),
                       ('uniform t even, g=f1 (m\'=(t-1,t..t))', (1,0,0,0,0,0,0), [1]),
                       ('uniform t odd, g=f1', (0,1,1,1,1,1,1), [1])]:
    for g in gs:
        ranges = [range(-K - (K + p) % 2, K + 2, 2) for p in mpar]
        ranges = [[x for x in r if abs(x) <= K + 1 and (x - p) % 2 == 0] for r, p in zip(ranges, mpar)]
        pos = neg = 0; pos_sym = 0; pos_cls = 0; seen = set(); worst = Fraction(0)
        for e in itertools.product(*ranges):
            v = phi0(e, g)
            pos += v > 0; neg += v < 0
            s = phisym(e, g); pos_sym += s > 0
            key = tuple(abs(x) for x in e)
            if key not in seen:
                seen.add(key)
                cls = [ [sg * x for sg, x in zip(sgn, key)] for sgn in itertools.product([1, -1], repeat=7)]
                avg = sum(phi0(c, g) for c in cls) / len(cls)
                if avg > 0:
                    pos_cls += 1
                    worst = max(worst, avg)
        print(name, 'K', K, ': pointwise >0:', pos, '<0:', neg, '| symmetrised >0:', pos_sym, '| sign-class avg >0:', pos_cls, 'worst', worst, flush=True)
