#!/usr/bin/env python3
"""Finite checks for the K_n - e crossing-number candidate (stdlib only).

Checks (exact rational arithmetic unless stated):
 A. two-page drawing: total = Z(n), edge {0,t} has C(t,2) crossings, max edge = C(t,2).
 B. cycle identity for chains z_A on K_n - e when A(t1,t2)=A(t2,t1), and failure
    of the identity for generic A (the missing-edge condition matters).
 C. localization tests H = P*(u-v)(u-y)(v-x)*U(x)V(y)*(v-t_js)B'(u,v) are valid tests.
 D. E(S_a(al,be)) is orthogonal to E(S_b(be,al)) for the diagonal form a_alpha.
 E. E is injective on S_a(al,be) and S_b(be,al) (rank mod a 61-bit prime;
    full rank mod p implies full rank over Q), and |T| >= 2 dim S_a.
 F. corollary formula for cr(K_m x P_n) equals Zheng et al. conjecture (1.2).
 G. range in which OWH Thm 3.1 + upstream Harary-Hill + integrality already give odd n.
 H. floor-product form of the target and its parity forms, N <= 2000.
 I. twisted order detector: M(A,(v-u_c)B') = 0 for all B' in P_{s-1,s-2} forces A = 0.
 J. OWH Thm 3.2 bound (m+2)/(m-2) Z(m-1) equals the target for even m.
Drawings: two-page (upstream construction) minus its max edge, and random
rectilinear drawings minus an edge (all good drawings: adjacent edges do not cross).
"""
import itertools, random, math, sys
from fractions import Fraction as Fr
from math import comb

PR = 2**61 - 1

def Z(n): return (n//2)*((n-1)//2)*((n-2)//2)*((n-3)//2)//4
def target(n): return Z(n) - comb((n-1)//2, 2)

# ---------- drawings ----------
def twopage_J(n, removed=()):
    m = n//2
    page = {e: (1 if ((e[0]+e[1]) % n) < m else -1) for e in itertools.combinations(range(n), 2)}
    E = [e for e in itertools.combinations(range(n), 2) if e not in removed]
    J = {}
    ncross = 0
    for e, f in itertools.combinations(E, 2):
        a, b = e; c, d = f
        if len({a, b, c, d}) < 4 or page[e] != page[f]: continue
        if a < c < b < d: s = page[e]
        elif c < a < d < b: s = -page[e]
        else: continue
        ncross += 1
        J[(e, f)] = J.get((e, f), 0) + Fr(s); J[(f, e)] = J.get((f, e), 0) - Fr(s)
    for w in range(n):
        inc = [e for e in E if w in e]
        def key(e):
            o = e[0] if e[1] == w else e[1]; L = abs(o-w); up = page[e] == 1; right = o > w
            if up and right: return (0, L)
            if up: return (1, -L)
            if not right: return (2, L)
            return (3, -L)
        order = sorted(inc, key=key)
        for x, y in itertools.combinations(order, 2):
            sx = 1 if x[0] == w else -1; sy = 1 if y[0] == w else -1
            J[(x, y)] = J.get((x, y), 0) + Fr(sx*sy, 2); J[(y, x)] = J.get((y, x), 0) - Fr(sx*sy, 2)
    return E, J, ncross, page

def seg_cross(p1, p2, p3, p4):
    o = lambda a, b, c: (b[0]-a[0])*(c[1]-a[1])-(b[1]-a[1])*(c[0]-a[0])
    return o(p3, p4, p1)*o(p3, p4, p2) < 0 and o(p1, p2, p3)*o(p1, p2, p4) < 0

def rect_J(pts, removed=()):
    n = len(pts)
    E = [e for e in itertools.combinations(range(n), 2) if e not in removed]
    J = {}
    for e, f in itertools.combinations(E, 2):
        if len(set(e) | set(f)) < 4: continue
        A, B = pts[e[0]], pts[e[1]]; C, D = pts[f[0]], pts[f[1]]
        if seg_cross(A, B, C, D):
            de = (B[0]-A[0], B[1]-A[1]); df = (D[0]-C[0], D[1]-C[1])
            s = 1 if de[0]*df[1]-de[1]*df[0] > 0 else -1
            J[(e, f)] = Fr(s); J[(f, e)] = Fr(-s)
    for w in range(n):
        inc = [e for e in E if w in e]
        def ang(e):
            o = e[0] if e[1] == w else e[1]
            return math.atan2(pts[o][1]-pts[w][1], pts[o][0]-pts[w][0]) % (2*math.pi)
        order = sorted(inc, key=ang)
        for x, y in itertools.combinations(order, 2):
            sx = 1 if x[0] == w else -1; sy = 1 if y[0] == w else -1
            J[(x, y)] = J.get((x, y), 0) + Fr(sx*sy, 2); J[(y, x)] = J.get((y, x), 0) - Fr(sx*sy, 2)
    return E, J

def relabel(n, E, J, me):
    """relabel vertices so that missing edge me becomes (0,1)."""
    order = [me[0], me[1]] + [v for v in range(n) if v not in me]
    rl = {v: i for i, v in enumerate(order)}
    def re(e):
        a, b = rl[e[0]], rl[e[1]]; return ((a, b) if a < b else (b, a)), (1 if a < b else -1)
    J2 = {}
    for (e, f), v in J.items():
        (e2, se), (f2, sf) = re(e), re(f)
        J2[(e2, f2)] = v*se*sf
    return [re(e)[0] for e in E], J2

# ---------- polynomial helpers ----------
def nodes(n):
    return [Fr(3*i*i + i + 1) for i in range(n)]

def weights(t):
    n = len(t)
    return [1/math.prod((t[i]-t[j] for j in range(n) if j != i), start=Fr(1)) for i in range(n)]

def Jfull(J, e, f):
    """J on ordered vertex pairs (i,p),(k,q) with [pi]=-[ip]; J'=0 on missing edges."""
    se = 1; sf = 1
    if e[0] > e[1]: e = (e[1], e[0]); se = -1
    if f[0] > f[1]: f = (f[1], f[0]); sf = -1
    return se*sf*J.get((e, f), 0)

def test_sum(n, J, t, w, H, Eset):
    tot = Fr(0)
    for (i, p) in itertools.permutations(range(n), 2):
        e = (min(i, p), max(i, p))
        if e not in Eset: continue
        for (k, q) in itertools.permutations(range(n), 2):
            f = (min(k, q), max(k, q))
            if f not in Eset: continue
            jv = Jfull(J, (i, p), (k, q))
            if jv == 0: continue
            tot += jv*w[i]*w[p]*w[k]*w[q]*H(t[i], t[p], t[k], t[q])
    return tot

def symbasis(d): return [(a, b) for a in range(d+1) for b in range(a, d+1)]
def symval(ab, x, u):
    a, b = ab
    return x**a*u**b + (x**b*u**a if a != b else 0)

def rank_mod(M):
    M = [[int(x) % PR for x in r] for r in M]; r = 0
    ncol = len(M[0]) if M else 0
    for c in range(ncol):
        piv = next((i for i in range(r, len(M)) if M[i][c]), None)
        if piv is None: continue
        M[r], M[piv] = M[piv], M[r]; inv = pow(M[r][c], PR-2, PR)
        M[r] = [x*inv % PR for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c]:
                f = M[i][c]; M[i] = [(a-f*b) % PR for a, b in zip(M[i], M[r])]
        r += 1
    return r

def nullspace_Q(rows, ncol):
    """exact rational nullspace basis"""
    M = [list(map(Fr, r)) for r in rows]; piv = []; r = 0
    for c in range(ncol):
        p = next((i for i in range(r, len(M)) if M[i][c] != 0), None)
        if p is None: continue
        M[r], M[p] = M[p], M[r]; v = M[r][c]; M[r] = [x/v for x in M[r]]
        for i in range(len(M)):
            if i != r and M[i][c] != 0:
                f = M[i][c]; M[i] = [a-f*b for a, b in zip(M[i], M[r])]
        piv.append(c); r += 1
    basis = []
    for fc in [c for c in range(ncol) if c not in piv]:
        v = [Fr(0)]*ncol; v[fc] = Fr(1)
        for i, pc in enumerate(piv): v[pc] = -M[i][fc]
        basis.append(v)
    return basis

def space(al, be, cond, t):
    """basis (as coefficient vectors over product sym basis) of S(al,be) with
    cond 'a': P(t0,t1,y,v)=0 ; 'b': P(x,u,t0,t1)=0."""
    B1, B2 = symbasis(al), symbasis(be)
    basis = [(p, q) for p in B1 for q in B2]
    rows = []
    if cond == 'a':
        for q0 in B2: rows.append([symval(p, t[0], t[1]) if q == q0 else 0 for (p, q) in basis])
    if cond == 'b':
        for p0 in B1: rows.append([symval(q, t[0], t[1]) if p == p0 else 0 for (p, q) in basis])
    K = nullspace_Q(rows, len(basis)) if rows else [[Fr(int(i == j)) for j in range(len(basis))] for i in range(len(basis))]
    def make(vec):
        def P(x, u, y, v):
            return sum(c*symval(p, x, u)*symval(q, y, v) for c, (p, q) in zip(vec, basis) if c != 0)
        return P
    return basis, K, make

def params(n):
    s = n//2
    return (s-2, s-2) if n % 2 else (s-2, s-3)

def Tset(J):
    return [(e, f) for (e, f), v in J.items() if v != 0 and len(set(e) | set(f)) == 4]

# ---------- checks ----------
def check_A(maxn=40):
    for n in range(4, maxn+1):
        E, J, nc, page = twopage_J(n)
        tt = (n-1)//2
        cnt = {e: 0 for e in E}
        for (e, f), v in J.items():
            if len(set(e) | set(f)) == 4 and v != 0: cnt[e] += 1
        assert nc == Z(n), (n, nc)
        assert cnt[(0, tt)] == comb(tt, 2), (n, cnt[(0, tt)])
        assert max(cnt.values()) == comb(tt, 2)
    print(f"A ok: two-page total=Z(n), edge (0,t) has C(t,2) crossings = max, n=4..{maxn}")

def drawings(n, seed):
    out = []
    E, J, nc, page = twopage_J(n, removed=((0, (n-1)//2),))
    E2, J2 = relabel(n, E, J, (0, (n-1)//2))
    out.append(('twopage-minus-max', E2, J2))
    rnd = random.Random(seed)
    for k in range(2):
        pts = [(rnd.random(), rnd.random()) for _ in range(n)]
        me = (0, 1) if k == 0 else (2, n-1)
        E, J = rect_J(pts, removed=(me,))
        E2, J2 = relabel(n, E, J, me)
        out.append((f'rect{k}', E2, J2))
    return out

def check_BC(ns=(7, 8, 9)):
    rnd = random.Random(1)
    for n in ns:
        t = nodes(n); w = weights(t)
        for name, E, J in drawings(n, 100+n):
            Es = set(E); d = n-2
            def randA(sym_at_edge):
                c = [[rnd.randint(-3, 3) for _ in range(d+1)] for _ in range(d+1)]
                A = lambda x, u: sum(c[a][b]*x**a*u**b for a in range(d+1) for b in range(d+1))
                if not sym_at_edge: return A
                delta = A(t[0], t[1]) - A(t[1], t[0])
                # subtract delta * x^0 u^1 / (t1 - t0) to restore A(t0,t1)=A(t1,t0)
                return lambda x, u: A(x, u) - delta*u/(t[1]-t[0])
            A = randA(True); B = randA(True)
            v_ok = test_sum(n, J, t, w, lambda x, u, y, v: A(x, u)*B(y, v), Es)
            A2 = randA(False); B2 = randA(False)
            v_bad = test_sum(n, J, t, w, lambda x, u, y, v: A2(x, u)*B2(y, v), Es)
            assert v_ok == 0, (n, name, v_ok)
            # localization tests with random P in S_a (not necessarily kernel)
            al, be = params(n); s = n//2
            basis, K, make = space(al, be, 'a', t)
            cf = [rnd.randint(-2, 2) for _ in K]
            vec = [sum(c*k[i] for c, k in zip(cf, K)) for i in range(len(basis))]
            P = make(vec)
            assert P(t[0], t[1], Fr(5), Fr(7)) == 0 and P(t[1], t[0], Fr(3), Fr(11)) == 0
            for j, js in ((0, 1), (1, 0)):
                if n % 2: degU, degV1, du, dv = s, s-1, s-1, s-2
                else: degU, degV1, du, dv = s-1, s-1, s-2, s-2
                cu = [rnd.randint(-2, 2) for _ in range(degU+1)]
                cv = [rnd.randint(-2, 2) for _ in range(degV1+1)]
                cb = [[rnd.randint(-2, 2) for _ in range(dv+1)] for _ in range(du+1)]
                U = lambda x: sum(c*x**a for a, c in enumerate(cu))
                V = lambda y: (y-t[js])*sum(c*y**a for a, c in enumerate(cv))
                Bp = lambda u, v: (v-t[js])*sum(cb[a][b]*u**a*v**b for a in range(du+1) for b in range(dv+1))
                H = lambda x, u, y, v: P(x, u, y, v)*(u-v)*(u-y)*(v-x)*U(x)*V(y)*Bp(u, v)
                val = test_sum(n, J, t, w, H, Es)
                assert val == 0, (n, name, 'loc', j, val)
            print(f"B/C ok n={n} {name}: valid tests vanish; generic invalid test value {'nonzero' if v_bad != 0 else 'zero'}")

def form_coeff(J, t, w, e, f):
    i, p = e; k, q = f
    x, u, y, v = t[i], t[p], t[k], t[q]
    Dl = (x-u)*(y-v)*(x-y)*(x-v)*(u-y)*(u-v)
    return J[(e, f)]*w[i]*w[p]*w[k]*w[q]*Dl

def check_DE(ns=(7, 8, 9, 10, 11, 12), full=False):
    for n in ns:
        t = nodes(n); w = weights(t); al, be = params(n)
        for name, E, J in drawings(n, 200+n):
            T = Tset(J)
            ba, Ka, mka = space(al, be, 'a', t)
            bb, Kb, mkb = space(be, al, 'b', t)
            Pa = [mka(k) for k in Ka]; Qb = [mkb(k) for k in Kb]
            EA = [[P(t[e[0]], t[e[1]], t[f[0]], t[f[1]]) for (e, f) in T] for P in Pa]
            EB = [[Q(t[e[0]], t[e[1]], t[f[0]], t[f[1]]) for (e, f) in T] for Q in Qb]
            coef = [form_coeff(J, t, w, e, f) for (e, f) in T]
            assert all(c != 0 for c in coef)
            # orthogonality (exact) on a subset of pairs for speed, all pairs when small
            pairs = [(i, j) for i in range(len(EA)) for j in range(len(EB))]
            if len(pairs) > 400 and not full:
                pairs = random.Random(n).sample(pairs, 400)
            for i, j in pairs:
                val = sum(c*a*b for c, a, b in zip(coef, EA[i], EB[j]))
                assert val == 0, (n, name, i, j, val)
            def modrows(M):
                out = []
                for r in M:
                    rr = []
                    for x in r:
                        rr.append(x.numerator*pow(x.denominator, PR-2, PR) % PR)
                    out.append(rr)
                return out
            ra = rank_mod(modrows(EA)); rb = rank_mod(modrows(EB))
            dimSa = len(Ka)
            assert dimSa == target(n), (n, dimSa, target(n))
            assert ra == dimSa and rb == len(Kb), (n, name, ra, rb, dimSa)
            assert len(T) >= 2*dimSa
            cr = len(T)//2
            print(f"D/E ok n={n} {name}: |T|/2={cr} >= target {target(n)}; rank E|S_a={ra}=dim, rank E|S_b={rb}=dim; orth checked on {len(pairs)} pairs")

def check_F(maxm=200):
    for m in range(4, maxm+1):
        c = Fr((m+1)//2*((m-1)//2)*((m-2)//2), 4)
        for n in range(1, 8):
            zheng = c*(n*((m+4)//2) + (m-4)//2)
            ours = (n-1)*target(m+2) + 2*Z(m+1)
            assert zheng == ours, (m, n)
    print(f"F ok: (n-1)cr(K_(m+2)-e)+2cr(K_(m+1)) = Zheng formula, 4<=m<={maxm}, 1<=n<=7")

def check_G(maxs=40):
    closes = []
    for s in range(2, maxs+1):
        m = 2*s+1
        lb = Fr(2*Z(m-1) + (m-2)*(Z(m) - (m-3)//2), m)
        ok = math.ceil(lb) >= target(m)
        closes.append((m, ok))
        assert (lb == target(m) - Fr((s-1)*(s-2), 2*(2*s+1)))
    good = [m for m, ok in closes if ok]; bad = [m for m, ok in closes if not ok]
    print(f"G: OWH Thm3.1 + HH + integrality closes odd n in {good[:10]}...; fails for odd n from {bad[0]} on (checked to n={2*maxs+1}); all failures: {bad==[m for m,_ in closes if m>=15]}")

def check_H(maxn=2000):
    for N in range(1, maxn+1):
        prod4 = ((N+2)//2)*((N-1)//2)*((N-3)//2 if N >= 3 else 0)*((N-4)//2 if N >= 4 else 0)
        assert 4*target(N) == prod4, N
        s = N//2
        if N >= 5 and N % 2: assert target(N) == comb(s, 2)**2 - comb(s, 2)
        if N >= 6 and N % 2 == 0: assert target(N) == comb(s, 2)*comb(s-1, 2) - comb(s-1, 2)
    print(f"H ok: Z(N)-C(floor((N-1)/2),2) = (1/4)floor((N+2)/2)floor((N-1)/2)floor((N-3)/2)floor((N-4)/2), N<={maxn}")

def check_I(ss=(2, 3, 4, 5), trials=3):
    """twisted detector: A in P_{s-2,s-2}, M(A,(v-u_c)B')=0 for all B' in P_{s-1,s-2} => A=0,
    for random linear orders S and every choice of the node u_c."""
    rnd = random.Random(7)
    for s in ss:
        N = 2*s
        for _ in range(trials):
            u = [Fr(rnd.randint(-50, 50)*7 + k) for k in range(N)]
            assert len(set(u)) == N
            order = list(range(N)); rnd.shuffle(order); pos = {v: i for i, v in enumerate(order)}
            G1 = [math.prod((u[p]-u[q] for q in range(N) if q != p), start=Fr(1)) for p in range(N)]
            def S(p, q): return Fr(0) if p == q else (Fr(1, 2) if pos[p] < pos[q] else Fr(-1, 2))
            Abasis = [(a, b) for a in range(s-1) for b in range(s-1)]
            Bbasis = [(a, b) for a in range(s) for b in range(s-1)]
            for c in range(N):
                rows = []
                for (a1, b1) in Abasis:
                    row = []
                    for (a2, b2) in Bbasis:
                        tot = Fr(0)
                        for p in range(N):
                            for q in range(N):
                                if p == q: continue
                                tot += S(p, q)*(u[p]-u[q])/(G1[p]*G1[q])*u[p]**a1*u[q]**b1*(u[q]-u[c])*u[p]**a2*u[q]**b2
                        row.append(tot)
                    rows.append(row)
                M = [[x.numerator*pow(x.denominator, PR-2, PR) % PR for x in r] for r in rows]
                assert rank_mod(M) == len(Abasis), (s, c)
    print(f"I ok: twisted detector has full row rank (dim P_(s-2,s-2)) for s in {ss}, all node choices c")

def check_J(maxM=500):
    for M in range(3, maxM+1):
        m = 2*M
        assert Fr(m+2, m-2)*Z(m-1) == target(m), M
    print(f"J ok: (m+2)/(m-2)*Z(m-1) = target(m) for even m=6..{2*maxM}")

if __name__ == '__main__':
    check_I()
    check_J()
    check_H(2000)
    check_A(40)
    check_F(200)
    check_G(40)
    check_BC((7, 8))
    check_DE((7, 8, 9, 10, 11, 12))
    print("ALL CHECKS PASSED")
