# Local O(1/t) coefficient for a FIXED deviation shape c of a near-uniform profile with parity functional psi(m):
#   lim_{t->oo} t*(8 sigma(c) - 1) = 4 h_o * E_w[ 3*sum_a s1(pi_a, R_a) + sum_{a<b} s2(pi_a,pi_b; R_a,R_b) ]
# pi = parity functional of m - c, i.e. psi(m) xor sum_f c_f f;  w_f = sum of c_f signs;  R_a = sum_{f(a)=0} w_f.
# s1: 1-D lattice sum with density slope 1 (coefficient of rho');  s2: 2-D interaction with unit density.
# (derivation in PROOF.md, Part C; heuristic local expansion, checked against exact data)
from fractions import Fraction
from math import comb
import itertools, sys
def fval(f, a): return bin(f & a).count('1') & 1
def h1(z): return Fraction(1) if z > 0 else (Fraction(1, 2) if z == 0 else Fraction(0))
def h2(za, zb):
    if za < 0 or zb < 0: return Fraction(0)
    return Fraction(1, 1 + (za == 0) + (zb == 0))
S1 = {}; S2 = {}
def s1(p, y):
    if (p, y) not in S1:
        S1[(p, y)] = sum(2 * z * (h1(z + y) - h1(z)) for z in range(p - 40, 41, 2) if (z - p) % 2 == 0)
    return S1[(p, y)]
def s2(p, q, ya, yb):
    k = (p, q, ya, yb)
    if k not in S2:
        s = Fraction(0)
        for za in range(p - 30, 31, 2):
            for zb in range(q - 30, 31, 2):
                d = h2(za + ya, zb + yb) - h2(za, zb)
                d -= (h1(za + ya) - h1(za)) * (1 if zb > 0 else 0)
                d -= (h1(zb + yb) - h1(zb)) * (1 if za > 0 else 0)
                s += 4 * d
        S2[k] = s
    return S2[k]
ho = 0.00833056532535052
def Q(psi, c):
    pi = psi
    for f in range(1, 8):
        if c[f - 1] % 2: pi ^= f
    par = [fval(pi, a) for a in range(1, 8)]
    tot = Fraction(0)
    for wv in itertools.product(*[range(-k, k + 1, 2) for k in c]):
        wt = Fraction(1)
        for k, x in zip(c, wv): wt *= Fraction(comb(k, (k + x) // 2), 2 ** k)
        R = [sum(wv[f - 1] for f in range(1, 8) if fval(f, a) == 0) for a in range(1, 8)]
        v = 3 * sum(s1(par[i], R[i]) for i in range(7))
        v += sum(s2(par[i], par[j], R[i], R[j]) for i, j in itertools.combinations(range(7), 2))
        tot += wt * v
    return tot
if __name__ == '__main__':
    print('s1 table', {y: (str(s1(0, y)), str(s1(1, y))) for y in range(-3, 4)})
    K = int(sys.argv[1])
    for label, psi in [('psi=f1 (family (t+1,t,..,t))', 1), ('psi=0 (uniform)', 0)]:
        shapes = [c for c in itertools.product(range(K + 1), repeat=7) if 0 < sum(c) <= K]
        res = {c: Q(psi, c) for c in shapes}
        mx = max(res.values())
        print(label, ' max over 0<|c|<=%d of lim t(8sigma-1) = %.5f' % (K, 4 * ho * float(mx)), [c for c in res if res[c] == mx][:4])
        byk = {}
        for c, v in res.items(): byk.setdefault(sum(c), []).append(v)
        print('   by |c|: max', [(k, round(4 * ho * float(max(v)), 4)) for k, v in sorted(byk.items())],
              ' min', [(k, round(4 * ho * float(min(v)), 4)) for k, v in sorted(byk.items())])
        for c in [(1,0,0,0,0,0,0),(0,1,0,0,0,0,0),(2,0,0,0,0,0,0),(1,1,0,0,0,0,0),(0,1,1,0,0,0,0),(0,0,0,0,0,1,1)]:
            if sum(c) <= K: print('   c', c, '%.5f' % (4 * ho * float(res[c])))
