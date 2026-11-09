# Agent E: point-level coverage.  For each alive config with <=2 far digits, every placement class (positions of the far
# digits, any L) must be inside the declared domain of some certificate (or in L <= 300, the brute-force region).
# A certificate (K', coefs c_1..c_m, qmin) covers: K' = K0 + sum of the *fixed* far digits' A*10^p, the other far digits sit at
# positions q_1<...<q_m (carrying coefs c_1..c_m in that order), all >= qmin, L > q_m  (dim 1: L >= qmin).
import json, glob, os, collections, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from e_enum import *
C = '../glm/L2c/'
N = 100          # explicit positions 3..N, everything above handled symbolically
idx = {}         # (T, K', coefs) -> min qmin
for f in sorted(glob.glob(C + 'cert_t*.jsonl')):
    m = json.loads(open(f).readline())
    assert m['qmin'] > v2(m['K']) and m['root']['m'] == 1 and m['dim'] == len(m['coefs']) + 1 and m['K'] % 5
    kk = (m['target'], m['K'], tuple(m['coefs']))
    idx[kk] = min(idx.get(kk, 10**9), m['qmin'])
EXTRA = os.environ.get('E_EXTRA')   # 'hyp' = hypothetical reversed-order certs; 'real' = load indep2/certs_e/*.jsonl
if EXTRA == 'hyp':
    mj = json.load(open('e_missing.json'))
    for kk, n in mj:
        T, Kp, coefs, qmin = kk
        if len(coefs) == 2: idx[(T, Kp, tuple(coefs))] = min(idx.get((T, Kp, tuple(coefs)), 10**9), qmin)
if EXTRA == 'real':
    for f in sorted(glob.glob('certs_e/*.jsonl')):
        m = json.loads(open(f).readline())
        T = m.get('target')
        if T is None: continue
        kk = (T, m['K'], tuple(m['coefs'])); idx[kk] = min(idx.get(kk, 10**9), m['qmin'])
def cq(T, Kp, coefs):
    return idx.get((T, Kp, tuple(coefs)))
def cover_k0(T, K0):
    q = cq(T, K0, ())
    return q is not None and q <= 301
def cover_k1(T, K0, a):
    unc = []
    qn = cq(T, K0, (a,))
    for p in range(3, N + 1):
        ok = (qn is not None and p >= qn)
        if not ok:
            q2 = cq(T, K0 + a * 10 ** p, ())
            ok = q2 is not None and q2 <= 301
        if not ok: unc.append(p)
    # tail p > N: need the generic one-far cert with qmin <= N+1
    tail = (qn is not None and qn <= N + 1)
    return unc, tail
def cover_k2(T, K0, a, b):
    """digits with A-values a<=b (placed at pa,pb).  returns list of uncovered explicit classes and the symbolic-tail verdicts"""
    unc = []
    sym = {}
    def covered(pa, pb):     # digit a at pa, digit b at pb
        # none fixed
        lo_first = (a, b) if pa < pb else (b, a)
        q = cq(T, K0, lo_first)
        if q is not None and min(pa, pb) >= q: return True
        # a fixed at pa, b free at pb
        q = cq(T, K0 + a * 10 ** pa, (b,))
        if q is not None and pb >= q: return True
        q = cq(T, K0 + b * 10 ** pb, (a,))
        if q is not None and pa >= q: return True
        q = cq(T, K0 + a * 10 ** pa + b * 10 ** pb, ())
        return q is not None and q <= 301
    for pa in range(3, N + 1):
        for pb in range(3, N + 1):
            if pa == pb: continue
            if a == b and pa > pb: continue
            if not covered(pa, pb): unc.append((pa, pb))
    # symbolic tails (positions > N).  both > N, either order:
    orders = [(a, b)] if a == b else [(a, b), (b, a)]
    for od in orders:
        q = cq(T, K0, od); sym['both>N, lower-position digit coef %s' % (od,)] = (q is not None and q <= N + 1)
    # one > N, other = p <= N fixed
    for p in range(3, N + 1):
        for (fx, fr) in ((a, b), (b, a)) if a != b else ((a, b),):
            q = cq(T, K0 + fx * 10 ** p, (fr,))
            tailok = (q is not None and q <= N + 1)
            # alternative: also covered by none-fixed generic cert when p >= its qmin (both orders needed since fr may be below or above)
            if not tailok:
                # fr > N > p  => order (fx, fr) in position order
                q0 = cq(T, K0, (fx, fr))
                tailok = (q0 is not None and q0 <= p)
            if not tailok: sym['fixed %s at %d, other free > N' % (fx, p)] = False
    return unc, sym
res = {}
for T in TARGETS:
    R = dict(configs_checked=0, fully_covered=0, partial=[], cats=collections.Counter())
    for k, v in configs(T).items():
        if v['dead40'] or len(k[1]) >= 3: continue
        S, farA = k; K0 = 9 * S - 1; R['configs_checked'] += 1
        if len(farA) == 0:
            ok = cover_k0(T, K0); unc = [] if ok else ['dim1 missing']; sym = {}
        elif len(farA) == 1:
            u, tail = cover_k1(T, K0, farA[0]); unc = u; sym = {} if tail else {'tail': False}
        else:
            unc, sym = cover_k2(T, K0, *farA)
        badsym = [s for s, o in sym.items() if not o]
        if unc or badsym:
            R['partial'].append((k, len(unc), unc[:6], badsym[:4]))
        else: R['fully_covered'] += 1
    res[T] = R
    print('=== T', T, 'alive<=2far checked', R['configs_checked'], 'fully point-covered', R['fully_covered'], 'with holes', len(R['partial']))
    for k, n, u, bs in R['partial']: print('   hole', k, 'explicit-uncovered', n, u, bs)
json.dump({T: dict(R, cats=None) for T, R in res.items()}, open('e_point_out.json', 'w'), default=str, indent=1)
