"""VARIANT with base case M_{2,1,2}(u,v) = v b u (printed: u b v). Literal implementation of Hetyei (arXiv:2007.07362v2) Theorem 5.7 operator
   I2(u) = u + u* + sum_u M(u*_(1), u_(2))
with the Ehrenborg-Readdy coproduct Delta(v1..vn) = sum_i v1..v_{i-1} (x) v_{i+1}..vn,
u* = reversal, and the mixing operator M exactly as printed in Definition 5.6:
   M(u,v) = sum_{r,s in {1,2}} sum_n M_{r,s,n}(u,v),
   M_{1,2,2}(u,v) = u a v,  M_{2,1,2}(u,v) = u b v,
   M_{1,s,n+1}(u,v) = sum_u u_(1) a M_{2,s,n}(u_(2), v),
   M_{2,s,n+1}(u,v) = sum_v v_(1) b M_{1,s,n}(u, v_(2)),
   (all other M_{r,s,2} = 0).
Modes:
  compare NMAX : compare with the flag-f/Delannoy operator of hetyei_I2.py on every ab-word, n<=NMAX
  kernel N     : exact rational kernel of I2 on Q<a,b>_N, its symmetric part, printed in the ab-word basis
Usage: hetyei_literal.py compare NMAX | hetyei_literal.py kernel N   (needs SCRIPTDIR as argv[-1])"""
import sys, itertools, importlib.util
from fractions import Fraction
from functools import lru_cache
SD = sys.argv[-1]
spec = importlib.util.spec_from_file_location('h2', SD + '/hetyei_I2.py'); h2 = importlib.util.module_from_spec(spec); spec.loader.exec_module(h2)

def addto(d, w, c):
    if c:
        d[w] = d.get(w, 0) + c
        if d[w] == 0: del d[w]
def coprod(w):
    return [(w[:i], w[i + 1:]) for i in range(len(w))]
@lru_cache(None)
def Mrsn(r, s, n, u, v):
    """returns tuple of (word, coeff)"""
    out = {}
    if n < 2: return ()
    if n == 2:
        if (r, s) == (1, 2): addto(out, u + 'a' + v, 1)
        if (r, s) == (2, 1): addto(out, v + 'b' + u, 1)  # CORRECTED: printed 'u b v' read as 'v b u'
        return tuple(out.items())
    if r == 1:
        for u1, u2 in coprod(u):
            for w, c in Mrsn(2, s, n - 1, u2, v): addto(out, u1 + 'a' + w, c)
    else:
        for v1, v2 in coprod(v):
            for w, c in Mrsn(1, s, n - 1, u, v2): addto(out, v1 + 'b' + w, c)
    return tuple(out.items())
def M(u, v):
    out = {}
    for r in (1, 2):
        for s in (1, 2):
            for n in range(2, len(u) + len(v) + 3):
                for w, c in Mrsn(r, s, n, u, v): addto(out, w, c)
    return out
def I2word(u):
    out = {}
    addto(out, u, 1); addto(out, u[::-1], 1)
    for u1, u2 in coprod(u):
        for w, c in M(u1[::-1], u2).items(): addto(out, w, c)
    return out
# basis changes: word with b-set B  <->  flag-f basis
def f_to_ab(fvec, n):
    """fvec: dict mask->coeff (flag f basis). ab coefficient of word with b-set B = sum_{S subset B} f(S)(-1)^{|B-S|}"""
    out = {}
    for S, c in fvec.items():
        free = [i for i in range(n) if not S >> i & 1]
        for k in range(len(free) + 1):
            for extra in itertools.combinations(free, k):
                B = S
                for i in extra: B |= 1 << i
                w = ''.join('b' if B >> i & 1 else 'a' for i in range(n))
                addto(out, w, c * (-1) ** k)
    return out
def ab_to_f(abvec, n):
    """inverse: f(S) = sum_{B subset S} h(B)  (h = ab coefficients)"""
    out = {}
    for w, c in abvec.items():
        B = sum(1 << i for i in range(n) if w[i] == 'b')
        free = [i for i in range(n) if not B >> i & 1]
        for k in range(len(free) + 1):
            for extra in itertools.combinations(free, k):
                S = B
                for i in extra: S |= 1 << i
                addto(out, S, c)
    return out
def I2_flag_on_ab(u, n):
    fv = ab_to_f({u: 1}, n)
    res = {}
    for S, c in fv.items():
        for m, d in h2.I2_column(S, n).items(): addto(res, m, c * d)
    return f_to_ab(res, n)
def words(n): return [''.join(t) for t in itertools.product('ab', repeat=n)]

def rref_kernel(rows, ncols):
    """rows: list of lists (Fractions) representing the matrix A (each row = image coords of a basis vector,
    i.e. A^T). We want vectors x with sum_i x_i rows[i] = 0: kernel of the map basis_i -> rows[i]."""
    m = len(rows)
    # build augmented [rows | I]
    aug = [list(map(Fraction, rows[i])) + [Fraction(int(i == j)) for j in range(m)] for i in range(m)]
    r = 0
    for col in range(ncols):
        piv = next((i for i in range(r, m) if aug[i][col] != 0), None)
        if piv is None: continue
        aug[r], aug[piv] = aug[piv], aug[r]
        pv = aug[r][col]; aug[r] = [x / pv for x in aug[r]]
        for i in range(m):
            if i != r and aug[i][col] != 0:
                c = aug[i][col]; aug[i] = [x - c * y for x, y in zip(aug[i], aug[r])]
        r += 1
    return r, [row[ncols:] for row in aug[r:]]

if __name__ == '__main__':
    mode = sys.argv[1]
    if mode == 'compare':
        nmax = int(sys.argv[2]); bad = 0; tot = 0
        for n in range(0, nmax + 1):
            for u in words(n):
                tot += 1
                if I2word(u) != I2_flag_on_ab(u, n):
                    bad += 1
                    if bad < 5: print('DIFF', u, I2word(u), I2_flag_on_ab(u, n))
        # also check M = poset product on doubled chains is implied; and coproduct: no separate check
        print('compared words', tot, 'n<=', nmax, 'differences', bad)
    elif mode == 'kernel':
        n = int(sys.argv[2]); W = words(n); idx = {w: i for i, w in enumerate(W)}
        rows = []
        for u in W:
            img = I2word(u); row = [0] * len(W)
            for w, c in img.items(): row[idx[w]] = c
            rows.append(row)
        rk, ker = rref_kernel(rows, len(W))
        print('n', n, 'dim', len(W), 'rank I2 over Q', rk, 'kernel dim', len(ker), 'dim A_n', 2 ** (n - 1) - 2 ** ((n - 1) // 2))
        # symmetric part of kernel: project each kernel vector u -> (u + u*)/2 and find its span
        sym = []
        for v in ker:
            s = [Fraction(0)] * len(W)
            for i, w in enumerate(W):
                s[i] += v[i] / 2; s[idx[w[::-1]]] += v[i] / 2
            sym.append(s)
        # rank of sym vectors
        rs, _ = rref_kernel(sym, len(W)) if sym else (0, [])
        print('dim of symmetric projection of kernel =', rs)
        # print a basis of symmetric kernel vectors in lowest terms
        basis = []
        aug = [list(s) for s in sym]
        r = 0
        for col in range(len(W)):
            piv = next((i for i in range(r, len(aug)) if aug[i][col] != 0), None)
            if piv is None: continue
            aug[r], aug[piv] = aug[piv], aug[r]; pv = aug[r][col]; aug[r] = [x / pv for x in aug[r]]
            for i in range(len(aug)):
                if i != r and aug[i][col] != 0:
                    c = aug[i][col]; aug[i] = [x - c * y for x, y in zip(aug[i], aug[r])]
            r += 1
        from math import lcm, gcd
        for row in aug[:r]:
            L = 1
            for x in row: L = lcm(L, x.denominator)
            ints = [int(x * L) for x in row]
            g = 0
            for x in ints: g = gcd(g, x)
            ints = [x // g for x in ints]
            vec = {W[i]: ints[i] for i in range(len(W)) if ints[i]}
            # verify exactly with the literal operator
            img = {}
            for w, c in vec.items():
                for w2, d in I2word(w).items(): addto(img, w2, c * d)
            symm = all(vec.get(w[::-1], 0) == c for w, c in vec.items())
            print('SYMMETRIC KERNEL VECTOR', vec, '| I2(u)==0:', img == {}, '| u*==u:', symm)
