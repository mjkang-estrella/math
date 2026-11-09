# Exact deviator score sigma(c) for deviation shapes c of a subspace profile m, by enumerating the
# voter's signed agreements: u_f (on the m_f-c_f unmoved coords of class f) and w_f (on the c_f moved
# coords).  Deviator ties/beats opponent a iff K_a = sum_{f(a)=1} u_f - sum_{f(a)=0} w_f >= 0 (exact:
# 2(d(x,p_a)-d(x,v)) = 2K_a).  Integer weights prod C(size,(size+val)/2); exact Fractions.
# Usage: smallmoves.py MAXMOVE m1..m7      (all shapes with |c| <= MAXMOVE)
import sys; sys.path.insert(0, 'scripts')
from vk import np, fval, Fraction
from math import comb
import itertools
def classvals(k):
    return np.array([2 * i - k for i in range(k + 1)], dtype=np.int64), [comb(k, i) for i in range(k + 1)]
INC = [[fval(f, a) for f in range(1, 8)] for a in range(1, 8)]
def sigma(m, c):
    n = sum(m)
    assert n <= 62, 'int64 weight products exact only for n <= 62 (run sm_fam1_t10 predates this guard and is INVALID)'
    # u-grid
    vals = []; wts = []
    for f in range(7):
        v, w = classvals(m[f] - c[f]); vals.append(v); wts.append(np.array(w, dtype=np.int64))
    grids = np.meshgrid(*vals, indexing='ij', sparse=True)
    wg = np.meshgrid(*wts, indexing='ij', sparse=True)
    W = wg[0]
    for g in wg[1:]: W = W * g
    W = np.broadcast_to(W, tuple(len(v) for v in vals)).reshape(-1)
    La = []
    for a in range(7):
        acc = np.zeros(tuple(len(v) for v in vals), dtype=np.int16)
        for f in range(7):
            if INC[a][f]: acc = acc + grids[f].astype(np.int16)
        La.append(np.broadcast_to(acc, tuple(len(v) for v in vals)).reshape(-1))
    La = np.stack(La)  # 7 x N
    tot = Fraction(0)
    for wv in itertools.product(*[range(-c[f], c[f] + 1, 2) for f in range(7)]):
        ww = 1
        for f in range(7): ww *= comb(c[f], (c[f] + wv[f]) // 2)
        R = np.array([sum(wv[f] for f in range(7) if not INC[a][f]) for a in range(7)], dtype=np.int16)
        K = La - R[:, None]
        ok = np.all(K >= 0, axis=0)
        z = (K == 0).sum(axis=0)
        for tcount in range(8):
            sel = ok & (z == tcount)
            s = int(W[sel].sum())
            if s: tot += Fraction(ww * s, tcount + 1)
    return tot / 2 ** n
if __name__ == '__main__':
    K = int(sys.argv[1]); m = tuple(int(x) for x in sys.argv[2:9])
    shapes = [c for c in itertools.product(*[range(min(mf, K) + 1) for mf in m]) if 0 < sum(c) <= K]
    s0 = sigma(m, (0,) * 7)
    print('m', m, 'n', sum(m), 'sigma(0) =', s0)
    res = {}
    for c in shapes:
        s = sigma(m, c); res[c] = s
    best = max(res.values())
    print('max over 0<|c|<=%d: %.8f (x8)' % (K, float(best * 8)), 'EQ-locally' if best <= Fraction(1, 8) else 'PROFITABLE', [c for c in res if res[c] == best][:3])
    for c in sorted(res, key=lambda c: -res[c])[:8]:
        print('  c', c, 'sigma*8 = %.8f' % float(res[c] * 8), ' t*(1-8 sigma) = %.5f' % ((1 - float(res[c] * 8)) * (sum(m) / 7)), str(res[c]) if len(str(res[c])) < 60 else '')
