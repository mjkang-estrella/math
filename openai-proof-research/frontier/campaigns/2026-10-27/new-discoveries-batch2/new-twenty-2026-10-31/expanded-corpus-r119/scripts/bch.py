"""361213: dual of BCH code C_(q,q+1,3,h), q=p^s, h=(p-1)/2.  C^perp = {c_(a,b)=(Tr(a u^h + b u^(h+1)))_{u in U_{q+1}}}
(source Thm sec3 thm4, Delsarte).  Checks (1) the explicit Cayley-subline codeword a=w-w^(pq), b=w^(pq)-w^q has weight q-p,
(2) for small q, brute-force minimum weight over all (a,b) != 0 equals q-p."""
import sys, random
from sympy import factorint
def build(p, k):
    # GF(p^k) as ints 0..p^k-1 (base-p digit vectors); find primitive polynomial by random search; exp/log tables
    Q = p ** k; rnd = random.Random(7)
    def mulx(v, poly):  # v * x mod poly, v list of k coeffs low..high; poly monic coeffs low..high (k entries, leading 1 implied)
        top = v[-1]; w = [0] + v[:-1]
        return [(w[i] - top * poly[i]) % p for i in range(k)]
    fac = list(factorint(Q - 1))
    while True:
        poly = [rnd.randrange(p) for _ in range(k)]
        if poly[0] == 0: continue
        # build powers of x
        v = [0] * k; v[0] = 1; exp = []; seen = set(); okp = True
        for i in range(Q - 1):
            t = tuple(v)
            if t in seen: okp = False; break
            seen.add(t); exp.append(t); v = mulx(v, poly)
        if okp and v == [1] + [0] * (k - 1): break
    enc = lambda t: sum(c * p ** i for i, c in enumerate(t))
    E = [enc(t) for t in exp]; Lg = {e: i for i, e in enumerate(E)}
    def add(x, y):
        r, m = 0, 1
        for _ in range(k): r += ((x % p + y % p) % p) * m; x //= p; y //= p; m *= p
        return r
    def mul(x, y):
        if x == 0 or y == 0: return 0
        return E[(Lg[x] + Lg[y]) % (Q - 1)]
    def pw(x, e):
        if x == 0: return 0 if e else 1
        return E[(Lg[x] * e) % (Q - 1)]
    return Q, E, Lg, add, mul, pw
def neg(x, p, k):
    r, m = 0, 1
    for _ in range(k): r += ((-(x % p)) % p) * m; x //= p; m *= p
    return r
def run(p, s, brute):
    k = 2 * s; q = p ** s; h = (p - 1) // 2
    Q, E, Lg, add, mul, pw = build(p, k)
    U = [E[(q - 1) * i] for i in range(q + 1)]          # (q+1)-th roots of unity
    assert all(pw(u, q + 1) == 1 for u in U) and len(set(U)) == q + 1
    tr = lambda y: add(y, pw(y, q))
    def wt(a, b):
        return sum(1 for u in U if tr(add(mul(a, pw(u, h)), mul(b, pw(u, h + 1)))) != 0)
    w = E[1]  # primitive element, not in F_q since s>=1
    assert pw(w, q) != w
    wpq = pw(w, p * q)
    a = add(w, neg(wpq, p, k)); b = add(wpq, neg(pw(w, q), p, k))
    W = wt(a, b)
    res = {'p': p, 's': s, 'q': q, 'explicit_weight': W, 'q_minus_p': q - p}
    if brute:
        F = list(range(Q)); best = q + 1
        for a2 in F:
            for b2 in F:
                if a2 == 0 and b2 == 0: continue
                best = min(best, wt(a2, b2))
        res['brute_min_weight'] = best
    print(res, flush=True)
    return res
if __name__ == '__main__':
    for (p, s, br) in [(3, 2, True), (5, 2, True), (7, 2, False), (3, 3, False), (3, 4, False), (5, 3, False), (11, 2, False), (13, 2, False), (5, 4, False), (7, 3, False), (3, 6, False)]:
        r = run(p, s, br)
        assert r['explicit_weight'] == r['q_minus_p']
        if br: assert r['brute_min_weight'] == r['q_minus_p']
    print('ALL OK')
