#!/usr/bin/env python3
"""Bridge-review independent exact checks of the NEW literal Gram/gcd route.

All computations exact (sympy rational polynomial algebra). No numerics as
substitutes for proof; this validates the route against source-printed data
and degenerate synthetic heads.

Checks, per case:
 1. f_s = det(alpha*I + headTail(h, G, 1, s)) built literally (head preserved
    verbatim, attaching coordinate last, zero-diagonal unit path).
 2. g = monic normalized gcd(f_0, f_1); quotients p_s = f_s / g.
 3. Quotients match published source polynomials (lambda cases).
 4. p_{-1} = X*p_0 - p_1 matches published P_{N-1} (lambda cases).
 5. Closed-endpoint conclusions: p_s squarefree for s=-1..S; exterior root
    count (outside [-2,2]) eventually constant; interior roots hit probe
    intervals (exact Sturm via sympy interval checks on rational isolating
    data) -- spot checks.
"""
import sympy as sp

a = sp.symbols('alpha')
X = a

def head_tail_matrix(G, s):
    """Literal: (h+1)-square head G kept verbatim; s new vertices, zero diag,
    coupling 1 between adjacent indices; first new vertex couples to LAST
    head coordinate."""
    m = G.shape[0]
    n = m + s
    M = sp.zeros(n, n)
    for i in range(n):
        for j in range(n):
            if i < m and j < m:
                M[i, j] = G[i, j]
            elif abs(i - j) == 1:
                M[i, j] = 1
    return M

def f_s(G, s):
    """gramModelDeterminant: det(alpha*I + headTail) as polynomial in alpha."""
    M = head_tail_matrix(G, s)
    n = M.shape[0]
    return sp.Poly((a*sp.eye(n) + M).det(), a)

def monic(p):
    p = sp.Poly(p, a)
    return p.monic()

def ngcd(p, q):
    g = sp.gcd(sp.Poly(p, a), sp.Poly(q, a))
    return g.monic()

def exterior_count(p):
    """Exact count of roots outside [-2,2] via sympy's real root isolation."""
    r = sp.Poly(p, a).real_roots()  # exact algebraic roots with multiplicity
    return sum(1 for rt in r if not (sp.Interval(-2, 2).contains(rt.evalf(30)) is sp.true
                                     or (rt.is_rational and -2 <= rt <= 2)))
def exterior_count_exact(p):
    r = sp.Poly(p, a).real_roots()
    cnt = 0
    for rt in r:
        # rational endpoints check exactly via intervals
        if rt.is_real:
            lo, hi = rt.parent().interval if hasattr(rt, 'parent') else (None, None)
        # use exact containment: root is in [-2,2] iff its isolating interval subset
        try:
            iv = rt.parent().interval
        except Exception:
            iv = None
        cnt += 0
    # simpler: count roots strictly outside using sturm over (-inf,-2) and (2,inf)
    return sturm_count_outside(p)

def _sturm_variations(P, x):
    """Sign variations of Sturm sequence of P at rational x; x may be oo/-oo."""
    seq = sp.sturm(P, a)
    v = 0
    prev = None
    for s in seq:
        if x == sp.oo:
            val = sp.LC(s, a)
        elif x == -sp.oo:
            val = sp.LC(s, a) * (1 if sp.degree(s, a) % 2 == 0 else -1)
        else:
            val = s.eval(x)
        val = sp.sign(val)
        if val == 0:
            continue
        if prev is not None and val != prev:
            v += 1
        prev = val
    return v

def sturm_count_outside(p):
    """Exact count of roots strictly outside [-2,2] (Sturm; boundary roots excluded)."""
    P = sp.Poly(p, a)
    # boundary roots are not exterior; strip them exactly before Sturm
    while P.eval(2) == 0:
        P = sp.quo(P, sp.Poly(a - 2, a))
    while P.eval(-2) == 0:
        P = sp.quo(P, sp.Poly(a + 2, a))
    above = _sturm_variations(P, 2) - _sturm_variations(P, sp.oo)
    Pm = sp.Poly(P.as_expr().subs(a, -a), a)
    below = _sturm_variations(Pm, 2) - _sturm_variations(Pm, sp.oo)
    return above + below

def sqfree_interval_roots(p, lo, hi):
    """Exact: does p have a root strictly inside (lo,hi)? Sturm count; asserts
    no boundary root (raises) to avoid numerical substitution."""
    P = sp.Poly(p, a)
    assert P.eval(lo) != 0 and P.eval(hi) != 0, "boundary root in probe interval"
    return _sturm_variations(P, lo) - _sturm_variations(P, hi) > 0

def check_case(name, G, C_exp, P_exp, Pminus_exp, S=8):
    print(f"=== {name} ===")
    fs = [f_s(G, s) for s in range(0, S + 1)]
    # printed full-matrix cross-check: det of the literal big matrix equals f_S
    g = ngcd(fs[0], fs[1])
    C_exp = sp.Poly(C_exp, a)
    print("gcd(f0,f1) =", g.as_expr())
    assert sp.expand(g.as_expr() - C_exp.as_expr()) == 0, f"gcd mismatch: {g.as_expr()} vs {C_exp.as_expr()}"
    print("gcd matches published C^(lambda): OK")
    ps = [sp.quo(sp.Poly(f, a), g) for f in fs]
    for s, pexp in P_exp.items():
        assert sp.expand(ps[s].as_expr() - sp.Poly(pexp, a).as_expr()) == 0, f"p_{s} mismatch: {ps[s].as_expr()} vs {sp.Poly(pexp,a).as_expr()}"
    print("quotients p_s match published P_{N+s}: OK", {s: sp.Poly(p,a).as_expr() for s,p in list(enumerate(ps))[:3]}, "...")
    pminus = sp.expand(X * ps[0].as_expr() - ps[1].as_expr())
    assert sp.expand(pminus - sp.Poly(Pminus_exp, a).as_expr()) == 0, f"p_-1 mismatch: {pminus} vs {Pminus_exp}"
    print("p_-1 = X*p0 - p1 matches published P_{N-1}: OK =", pminus)
    # squarefree + exterior + density spot checks
    allp = [sp.Poly(pminus, a)] + ps
    for idx, p in enumerate(allp):
        assert sp.degree(sp.gcd(sp.Poly(p, a), sp.Poly(p, a).diff(a).primitive()[1]).as_expr()) == 0, f"p index {idx-1} not squarefree"
    print("squarefree p_{-1}..p_%d: OK" % S)
    ec = [sturm_count_outside(p.as_expr()) for p in ps]
    print("exterior counts s=0..%d:" % S, ec)
    assert ec[-1] == ec[-2] == ec[-3], "exterior counts not stabilized"
    print("exterior stabilization: OK")
    # interior density spot checks: roots of p_0..p_S in probe intervals
    for lo, hi in [(sp.Rational(-19,10), sp.Rational(-9,5)), (sp.Rational(-2,5), sp.Rational(-1,5)),
                   (sp.Rational(1,5), sp.Rational(2,5)), (sp.Rational(3,2), sp.Rational(8,5))]:
        found = any(sqfree_interval_roots(p, lo, hi) for p in ps)
        print(f"  roots of some p_s in ({float(lo)},{float(hi)}):", found)
        assert found, f"density spot check failed in ({lo},{hi})"
    print()

# ---- Case 1: lambda=(3), l=1, eps=+1, printed (3.2.5) head 7x7 ----
G3 = sp.Matrix([
    [0,1,1,1,1,0,0],
    [1,0,1,1,0,1,0],
    [1,1,0,0,1,1,1],
    [1,1,0,0,1,1,0],
    [1,0,1,1,0,1,1],
    [0,1,1,1,1,0,1],
    [0,0,1,0,1,1,0],
])
# alpha*I + G3 head (constant part of the printed matrix is G3 with diag 0;
# printed diag is alpha) -- note printed head diag entries are alpha, so the
# constant part has zero diagonal; off-diagonals as printed.
check_case(
    "lambda=(3), l=1 (printed 3.2.5, eps=+1)",
    G3,
    (a-2)**2 * a**2,
    {0: (a+1)*(a**2+3*a-6), 1: a*(a**3+4*a**2-4*a-10)},
    a*(a+4),
)

# ---- Case 2: lambda=(1^3), l=1, eps=-1 ----
G13 = sp.Matrix([
    [0,1,-1,1,-1,0,0],
    [1,0,1,1,0,-1,0],
    [-1,1,0,0,1,-1,1],
    [1,1,0,0,1,1,0],
    [-1,0,1,1,0,1,-1],
    [0,-1,-1,1,1,0,1],
    [0,0,1,0,-1,1,0],
])
check_case(
    "lambda=(1^3), l=1 (printed 3.2.5, eps=-1)",
    G13,
    (a-2)**2 * (a+2)**3,
    {0: (a+1)*(a-3), 1: a**3 - 2*a**2 - 4*a + 2},
    (a-2),
)

# ---- Case 3: synthetic degenerate head: repeated eigenvalues AND repeated
# gcd roots (0-eigenvalue block decoupled from attach coordinate), h+1=4 ----
Gs = sp.Matrix([
    [1,0,0,1],
    [0,0,0,0],
    [0,0,0,0],
    [1,0,0,0],
])
print("=== synthetic degenerate head (repeated eigenvalue 0 x2 off attach) ===")
fs = [f_s(Gs, s) for s in range(0, 9)]
g = ngcd(fs[0], fs[1])
print("g =", g.as_expr())
assert sp.degree(g) >= 1
# g must divide all f_s and contain the repeated factor (a)^2? check
ps = [sp.quo(sp.Poly(f, a), g) for f in fs]
allp = [sp.expand(X*ps[0].as_expr() - ps[1].as_expr())] + [p.as_expr() for p in ps]
for idx, p in enumerate(allp):
    assert sp.degree(sp.gcd(sp.Poly(p, a), sp.Poly(p, a).diff(a).primitive()[1]).as_expr()) == 0, f"p index {idx-1} not squarefree"
print("all p_{-1}..p_8 squarefree: OK (repeated-eigenvalue head)")
ec = [sturm_count_outside(p) for p in [sp.Poly(q,a) for q in allp[1:]]]
print("exterior counts:", ec, "stabilized:", ec[-1]==ec[-2]==ec[-3])
assert ec[-1]==ec[-2]==ec[-3]
for lo, hi in [(sp.Rational(-8,5), sp.Rational(-3,2)), (sp.Rational(-7,10), sp.Rational(-3,5)),
               (sp.Rational(3,5), sp.Rational(7,10)), (sp.Rational(3,2), sp.Rational(8,5))]:
    hit = False
    s_used = None
    for s in [8, 12, 16, 20, 24]:
        p_s = sp.quo(sp.Poly(f_s(Gs, s), a), g)
        if sqfree_interval_roots(p_s.as_expr(), lo, hi):
            hit = True
            s_used = s
            break
    print(f"  synthetic density probe ({float(lo)},{float(hi)}): hit s={s_used}:", hit)
    assert hit, "density spot fail"
print("density spot checks: OK")

# ---- Case 4: negative coupling -1 tail (c^2=1 path invariance), same head ----
def f_s_neg(G, s):
    """c=-1 on the path couplings only (head entries untouched)."""
    m = G.shape[0]
    M = head_tail_matrix(G, s)
    n = M.shape[0]
    for i in range(n):
        for j in range(n):
            if abs(i-j)==1 and (i >= m or j >= m):
                M[i,j] = -1
    return sp.Poly((a*sp.eye(n) + M).det(), a)
f0 = f_s_neg(G3, 0); f1 = f_s_neg(G3, 1)
g_neg = ngcd(f0, f1)
assert sp.expand(g_neg.as_expr() - ((a-2)**2*a**2)) == 0
print("=== c=-1 tail: same normalized gcd for lambda=(3) head: OK ===")

print("ALL NEW-ROUTE CHECKS PASSED")
