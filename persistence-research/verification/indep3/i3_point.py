# Agent E2: point-level coverage of every alive config with <= 2 far digits, by certificates.
# A certificate (T, K', coefs c_1..c_m, qmin) covers the placements where some subset of the far digits is FIXED
# (K' = K0 + sum fixed A*10^p), the m others sit at positions q_1<...<q_m>=qmin with coefs in position order, L > q_m.
# dim-1 certs cover L >= qmin (L <= 300 is the brute-force region).
# usage: python3 -I i3_point.py [extra_dir ...]       (extra_dir = directories with additional repair certs)
import json, glob, os, collections, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from i3_enum import *
B = '../glm/L2b/'
N = 100
idx = {}; src = {}
def load(fn, tag):
    m = json.loads(open(fn).readline())
    T = m.get('target')
    assert T in TARGETS, fn
    assert m['qmin'] > v2(m['K']) and m['root']['m'] == 1 and m['dim'] == len(m['coefs']) + 1, fn
    assert (m['K'] % 5 == 0) == bool(m.get('five', False)) and (m['K'] % 5 == 0) == (T == 15), fn
    assert m['K'] % 5 != 0 or T == 15
    kk = (T, m['K'], tuple(m['coefs']))
    if m['qmin'] < idx.get(kk, 10 ** 9): idx[kk] = m['qmin']; src[kk] = (tag, os.path.basename(fn))
for f in sorted(glob.glob(B + 'cert_t*.jsonl')): load(f, 'B')
for d in sys.argv[1:]:
    for f in sorted(glob.glob(d + '/*.jsonl')): load(f, 'E2')
def cq(T, Kp, coefs): return idx.get((T, Kp, tuple(coefs)))
def cover_k0(T, K0):
    q = cq(T, K0, ()); return q is not None and q <= 301
def cover_k1(T, K0, a):
    unc = []; qn = cq(T, K0, (a,))
    for p in range(3, N + 1):
        ok = qn is not None and p >= qn
        if not ok:
            q2 = cq(T, K0 + a * 10 ** p, ()); ok = q2 is not None and q2 <= 301
        if not ok: unc.append(p)
    return unc, (qn is not None and qn <= N + 1)
def cover_k2(T, K0, a, b):
    unc = []; sym = {}
    def covered(pa, pb):
        lo_first = (a, b) if pa < pb else (b, a)
        q = cq(T, K0, lo_first)
        if q is not None and min(pa, pb) >= q: return True
        q = cq(T, K0 + a * 10 ** pa, (b,))
        if q is not None and pb >= q: return True
        q = cq(T, K0 + b * 10 ** pb, (a,))
        if q is not None and pa >= q: return True
        q = cq(T, K0 + a * 10 ** pa + b * 10 ** pb, ())
        return q is not None and q <= 301
    for pa in range(3, N + 1):
        for pb in range(3, N + 1):
            if pa == pb: continue
            if a == b and pa > pb: continue          # equal digits: unordered
            if not covered(pa, pb): unc.append((pa, pb))
    for od in ([(a, b)] if a == b else [(a, b), (b, a)]):
        q = cq(T, K0, od); sym['both>N, lower-position digit order %s' % (od,)] = (q is not None and q <= N + 1)
    for p in range(3, N + 1):
        for (fx, fr) in (((a, b), (b, a)) if a != b else ((a, b),)):
            q = cq(T, K0 + fx * 10 ** p, (fr,))
            ok = q is not None and q <= N + 1
            if not ok:
                q0 = cq(T, K0, (fx, fr)); ok = q0 is not None and q0 <= p
            if not ok: sym['fixed %s at %d, other free > N' % (fx, p)] = False
    return unc, sym
if __name__ == '__main__':
    out = {}
    for T in TARGETS:
        cf = configs(T); R = collections.Counter(); holes = []; opens = []
        for k, v in sorted(cf.items()):
            S, farA = k; K0 = 9 * S - 1
            if v['dead_weak']: R['dead'] += 1; continue
            if len(farA) >= 3: R['alive>=3far'] += 1; opens.append(k); continue
            R['alive<=2far'] += 1
            if len(farA) == 0: ok = cover_k0(T, K0); unc = [] if ok else ['dim1 missing']; sym = {}
            elif len(farA) == 1:
                u, tail = cover_k1(T, K0, farA[0]); unc = u; sym = {} if tail else {'tail': False}
            else: unc, sym = cover_k2(T, K0, *farA)
            bs = [s for s, o in sym.items() if not o]
            if unc or bs: holes.append((k, v['multiset'], len(unc), unc[:5], bs[:3]))
            else: R['covered'] += 1
        out[T] = dict(R, holes=holes, open_ge3far=opens)
        print('T', T, 'total', len(cf), dict(R), 'holes', len(holes), 'alive>=3far (declared open by B?):', len(opens))
        for h in holes: print('    HOLE', h)
    json.dump({str(T): v for T, v in out.items()}, open('i3_point_out%s.json' % ('_repaired' if sys.argv[1:] else ''), 'w'), default=str, indent=1)
