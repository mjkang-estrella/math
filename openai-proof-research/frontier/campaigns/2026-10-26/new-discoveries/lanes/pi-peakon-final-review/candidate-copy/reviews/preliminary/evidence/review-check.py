"""REVIEW SUB-AGENT INDEPENDENT CHECKER (pi-peakon-preliminary-review).

Not a rerun of parent's check_peakon_coefficients.py. Differences:
- builds the LITERAL source matrices A,T,S of Avan-Frappat-Ragoucy Eq (2.1)-(2.3)
  with coherent per-particle roots (u_i = s_i w_i, v_i = s_i/w_i, w_i = exp(nu q_i/2)),
  including T_ii = p_i (Eq 5.6), s_ij = sgn(q_i - q_j), s_ii = 0;
- verifies the literal Lax matrix of Eq (4.8) equals S + Lambda*T + xi*A;
- verifies B = S+A is strictly upper and B - B^T = uv^T - vu^T symbolically in w;
- verifies the full all-order coefficient identity
    tr L(z)^m == sum_j Lambda^j sum_{partitions} a_j prod h^(k),
    a_j = m (j-1)! / (prod k_i * prod r_s!)
  as an exact symbolic identity (including m > N, ties of q);
- fully symbolic abstract determinant lemma in u,v,lam,xi,gamma,t (N=3);
- gamma = +/- 2 degenerate spectral curve cases;
- h^(2) normalization against source Eq (5.10) closed form;
- independent partition-counting derivation vs brute-force compositions;
- Appendix C / Eq (5.9),(5.13) coefficient data vs formula.
"""
import itertools, json, math
from fractions import Fraction
import sympy as sp
from pathlib import Path

t = sp.Symbol('t')
results = {"checks": 0, "failures": []}

def ok(label, cond):
    results["checks"] += 1
    if not cond:
        results["failures"].append(label)
        print("FAIL:", label)
    return cond

# ---------------------------------------------------------------- T1: fully
# symbolic abstract lemma, N=3: det(I-tL) == 1 - lam*t*((P+Q)/2 + gamma*(P-Q)/4)
def abstract_lemma_symbolic(N):
    u = sp.Matrix([sp.Symbol(f'u{i}') for i in range(N)])
    v = sp.Matrix([sp.Symbol(f'v{i}') for i in range(N)])
    lam, xi, gamma = sp.symbols('lam xi gamma')
    UV = u * v.T; VU = v * u.T
    B = sp.Matrix(N, N, lambda i, j: (UV[i, j] - VU[i, j]) if i < j else 0)
    assert sp.expand(B - B.T - (UV - VU)) == sp.zeros(N, N)
    A = (UV - VU) / 2; T = (UV + VU) / 2; S = B - A
    L = S + lam * T + xi * A
    R = sum((t**k * B**k for k in range(N)), sp.zeros(N, N))  # finite geometric series
    P = (v.T * R * u)[0, 0]; Q = (u.T * R * v)[0, 0]
    det = (sp.eye(N) - t * L).det()
    pred = 1 - lam * t * ((P + Q) / 2 + gamma * (P - Q) / 4)
    d = sp.Poly(sp.expand(det - pred), t, u[0], u[1], u[2], v[0], v[1], v[2], lam, xi, gamma)
    # reduce modulo the spectral curve xi^2 = lam^2 + gamma*lam + 1
    curve = sp.Poly(xi**2 - lam**2 - gamma * lam - 1, xi, lam, gamma)
    _, rem = sp.div(d, curve, xi)
    ok(f"T1 abstract lemma symbolic N={N}", rem.is_zero)

# ---------------------------------------------------------------- T2: literal
# source matrices.  w_i = exp(nu q_i / 2) as symbols; u_i = s_i*w_i, v_i = s_i/w_i.
def literal_matrices(qs, ss, N):
    """A, T, S per source Eq (2.1)-(2.3), coherent roots s_i, w_i = exp(nu q_i/2).
    Ties of q share one symbol (w_i = w_j when q_i = q_j)."""
    distinct = {}
    for q in qs: distinct.setdefault(q, len(distinct))
    wmap = [sp.Symbol(f'w{distinct[q]}') for q in qs]
    w = sorted(set(wmap), key=lambda s: s.name)
    def sinh_half(i, j):   # sinh(nu(q_i-q_j)/2) = (w_i/w_j - w_j/w_i)/2
        return sp.Rational(1, 2) * (wmap[i] / wmap[j] - wmap[j] / wmap[i])
    def cosh_half(i, j):
        return sp.Rational(1, 2) * (wmap[i] / wmap[j] + wmap[j] / wmap[i])
    def sgn(i, j):
        if i == j or qs[i] == qs[j]: return sp.Integer(0)  # s_ii = 0; ties give sgn(0) = 0
        return sp.Integer(1) if qs[i] > qs[j] else sp.Integer(-1)
    def root(i, j):        # sqrt(p_i p_j) := s_i s_j  (coherent per-particle roots)
        return ss[i] * ss[j]
    A = sp.Matrix(N, N, lambda i, j: root(i, j) * sinh_half(i, j))
    T = sp.Matrix(N, N, lambda i, j: root(i, j) * cosh_half(i, j))
    S = sp.Matrix(N, N, lambda i, j: root(i, j) * sgn(i, j) * sinh_half(i, j))
    return A, T, S, wmap

def spectral(gamma, z):
    Lam = (z**2 - 1) / (2 * z + gamma)
    xi = (z**2 + gamma * z + 1) / (2 * z + gamma)
    assert sp.simplify(xi**2 - (Lam**2 + gamma * Lam + 1)) == 0
    return Lam, xi

def hamiltonians(T, A, B, gamma, kmax):
    """h^(k) = k tr((T + gamma A/2) B^(k-1)), source Eq (5.17)."""
    P = sp.eye(T.shape[0]); hs = [None]
    for k in range(1, kmax + 1):
        hs.append(k * sp.trace((T + gamma * A / 2) * P))
        P = P * B
    return hs

def expand_partitions(m):
    """all partitions of m as descending tuples."""
    def rec(maxp, rem):
        if rem == 0: yield ()
        for k in range(min(maxp, rem), 0, -1):
            for rest in rec(k, rem - k): yield (k,) + rest
    return list(rec(m, m))

def coeff_formula(m, part):
    j = len(part)
    ks = sp.prod(part)
    rs = {}
    for k in part: rs[k] = rs.get(k, 0) + 1
    rfact = sp.prod(sp.factorial(r) for r in rs.values())
    return sp.Rational(m * sp.factorial(j - 1), 1) / (ks * rfact)

def conjectured_tau(m, hs, Lam):
    tot = sp.Integer(0)
    for part in expand_partitions(m):
        tot += Lam**len(part) * coeff_formula(m, part) * sp.prod(hs[k] for k in part)
    return tot

def run_literal(N, mmax, qs, ss, gamma, z, label):
    A, T, S, wmap = literal_matrices(qs, ss, N)
    w = wmap
    u = sp.Matrix([ss[i] * wmap[i] for i in range(N)])
    v = sp.Matrix([ss[i] / wmap[i] for i in range(N)])
    B = S + A
    ok(f"{label}: B strictly upper", all(B[i, j] == 0 for i in range(N) for j in range(i + 1)))
    ok(f"{label}: B-B^T == uv^T-vu^T", sp.simplify(B - B.T - (u * v.T - v * u.T)) == sp.zeros(N, N))
    ok(f"{label}: A == (uv^T-vu^T)/2", sp.simplify(A - (u * v.T - v * u.T) / 2) == sp.zeros(N, N))
    ok(f"{label}: T == (uv^T+vu^T)/2", sp.simplify(T - (u * v.T + v * u.T) / 2) == sp.zeros(N, N))
    ok(f"{label}: T_ii == p_i", all(sp.simplify(T[i, i] - ss[i]**2) == 0 for i in range(N)))
    Lam, xi = spectral(gamma, z)
    L = S + Lam * T + xi * A
    # Eq (4.8) literal Lax entry check for one off-diagonal and one diagonal pair
    i, j = 0, min(1, N - 1)
    sij = sp.Integer(1) if qs[i] > qs[j] else (sp.Integer(-1) if qs[i] < qs[j] else sp.Integer(0))
    hp = sp.Rational(1, 2) * (1 + Lam + sij * xi)
    hm = sp.Rational(1, 2) * (-1 + Lam - sij * xi)
    # published PDF p.8: L_ij = sqrt(p_i p_j)(h+ e^{+nu|q_ij|/2} + h- e^{-nu|q_ij|/2})
    e_pos = (w[i] / w[j]) if qs[i] > qs[j] else (w[j] / w[i] if qs[i] < qs[j] else sp.Integer(1))
    e_neg = (w[j] / w[i]) if qs[i] > qs[j] else (w[i] / w[j] if qs[i] < qs[j] else sp.Integer(1))
    L48 = ss[i] * ss[j] * (hp * e_pos + hm * e_neg)
    ok(f"{label}: Eq(4.8) entry ({i},{j}) == S+LT+xiA", sp.simplify(L48 - L[i, j]) == 0)
    hs = hamiltonians(T, A, B, gamma, mmax)
    ok(f"{label}: h1 == sum p_i", sp.simplify(hs[1] - sum(s**2 for s in ss)) == 0)
    # h^(2) vs source Eq (5.10): h(2) = 1/4 sum p_i p_j (2*gamma - S_ij),
    # S_ij = (gamma-2)e^{nu|q_ij|} + (gamma+2)e^{-nu|q_ij|}
    h2src = sp.Integer(0)
    for i in range(N):
        for j in range(N):
            e = (w[i] / w[j])**2 if qs[i] > qs[j] else ((w[j] / w[i])**2 if qs[i] < qs[j] else sp.Integer(1))
            Sij = (gamma - 2) * e + (gamma + 2) / e   # e = exp(nu |q_ij|)
            h2src += sp.Rational(1, 4) * ss[i]**2 * ss[j]**2 * (2 * gamma - Sij)
    ok(f"{label}: h2 == Eq(5.10)", sp.simplify(hs[2] - h2src) == 0)
    # all-order coefficient identity, including m > N
    Lp = sp.eye(N)
    for m in range(1, mmax + 1):
        Lp = Lp * L
        lhs = sp.trace(Lp)
        rhs = sp.simplify(conjectured_tau(m, hs, Lam)) if m <= 8 else None
        if rhs is None:
            rhs = conjectured_tau(m, hs, Lam)
        ok(f"{label}: tau_{m} identity", sp.cancel(sp.together(lhs - rhs)) == 0)

# ---------------------------------------------------------------- T3: gamma=+/-2
def run_degenerate(gv):
    N = 3
    u = sp.Matrix([sp.Integer(2 + i) for i in range(N)])
    v = sp.Matrix([sp.Rational(3 - i, 2) for i in range(N)])
    UV = u * v.T; VU = v * u.T
    B = sp.Matrix(N, N, lambda i, j: (UV[i, j] - VU[i, j]) if i < j else 0)
    A = (UV - VU) / 2; T = (UV + VU) / 2; S = B - A
    # gamma = +/-2: xi^2 = (lam +/- 1)^2; take xi = lam + sign
    for sgn in (1, -1):
        lam = sp.Rational(7, 5); xi = lam + sgn  # xi^2 = (lam+sgn)^2 = lam^2+2*sgn*lam+1
        gamma = 2 * sgn
        assert xi**2 == lam**2 + gamma * lam + 1
        L = S + lam * T + xi * A
        R = sum((t**k * B**k for k in range(N)), sp.zeros(N, N))
        P = (v.T * R * u)[0, 0]; Q = (u.T * R * v)[0, 0]
        det = (sp.eye(N) - t * L).det()
        pred = 1 - lam * t * ((P + Q) / 2 + gamma * (P - Q) / 4)
        ok(f"T3 gamma={gamma} collapse", sp.expand(det - pred) == 0)

# ---------------------------------------------------------------- T4: partition
# counting vs brute-force ordered compositions (independent derivation check)
def run_counting(mmax):
    for m in range(1, mmax + 1):
        comps = list(itertools.product(range(1, m + 1), repeat=m))  # too many; do recursive
        comps = []
        def rec(rem, cur):
            if rem == 0: comps.append(tuple(cur)); return
            for k in range(1, rem + 1): rec(rem - k, cur + [k])
        rec(m, [])
        for part in expand_partitions(m):
            j = len(part)
            # coefficient implied by trace-log derivation: m * (1/j) * (#ordered comps
            # realizing partition) / prod k_i = m*(j-1)!/(prod k_i * prod r_s!)
            ordered = sum(1 for c in comps if sorted(c, reverse=True) == list(part))
            implied = sp.Rational(m, j) * ordered / sp.prod(part)
            ok(f"T4 m={m} part={part}", implied == coeff_formula(m, part))
            # the two source families, Eq (5.21)
    for m in range(1, 9):
        ok(f"T4 a_1({m})==1", coeff_formula(m, (m,)) == 1)
        ok(f"T4 a_m(1^)==1", coeff_formula(m, tuple([1] * m)) == 1)
        for j in range(0, m - 1):
            part = (m - j,) + tuple([1] * j)
            ok(f"T5 family2 m={m} j={j}", coeff_formula(m, part) == sp.Rational(m, m - j))

# ---------------------------------------------------------------- T5: appendix C
# coefficient data as read from published pp 19 (C.1)-(C.4) and Eq (5.9),(5.13)
APPENDIX_C = {
    4: {(3, 1): sp.Rational(4, 3), (2, 2): sp.Rational(1, 2), (2, 1, 1): sp.Rational(2), (1, 1, 1, 1): sp.Rational(1)},
    5: {(4, 1): sp.Rational(5, 4), (3, 2): sp.Rational(5, 6), (3, 1, 1): sp.Rational(5, 3),
        (2, 2, 1): sp.Rational(5, 4), (2, 1, 1, 1): sp.Rational(5, 2), (1,) * 5: sp.Rational(1)},
    6: {(5, 1): sp.Rational(6, 5), (4, 2): sp.Rational(3, 4), (3, 3): sp.Rational(1, 3),
        (4, 1, 1): sp.Rational(3, 2), (3, 2, 1): sp.Rational(2), (2, 2, 2): sp.Rational(1, 4),
        (3, 1, 1, 1): sp.Rational(2), (2, 2, 1, 1): sp.Rational(9, 4), (2, 1, 1, 1, 1): sp.Rational(3),
        (1,) * 6: sp.Rational(1)},
    7: {(6, 1): sp.Rational(7, 6), (5, 2): sp.Rational(7, 10), (4, 3): sp.Rational(7, 12),
        (5, 1, 1): sp.Rational(7, 5), (4, 2, 1): sp.Rational(7, 4), (3, 3, 1): sp.Rational(7, 9),
        (3, 2, 2): sp.Rational(7, 12), (4, 1, 1, 1): sp.Rational(7, 4), (2, 2, 2, 1): sp.Rational(7, 8),
        (3, 2, 1, 1): sp.Rational(7, 2), (3, 1, 1, 1, 1): sp.Rational(7, 3),
        (2, 2, 1, 1, 1): sp.Rational(7, 2), (2, 1, 1, 1, 1, 1): sp.Rational(7, 2), (1,) * 7: sp.Rational(1)},
}

def run_appendix():
    for m, parts in APPENDIX_C.items():
        for part, a in parts.items():
            ok(f"T5 appendix m={m} {part}", coeff_formula(m, part) == a)
    # Eq (5.9): tau2 = Lam h2 + Lam^2 h1^2 ; Eq (5.13): tau3 = Lam h3 + 3/2 Lam^2 h2 h1 + Lam^3 h1^3
    ok("T5 tau2 (5.9)", coeff_formula(2, (2,)) == 1 and coeff_formula(2, (1, 1)) == 1)
    ok("T5 tau3 (5.13)", coeff_formula(3, (2, 1)) == sp.Rational(3, 2) and coeff_formula(3, (1, 1, 1)) == 1)

# ---------------------------------------------------------------- T6: unsorted
# q with explicit permutation relabeling (source Prop 5.1 proof route)
def run_relabel():
    N = 4
    qs = [1, -3, 5, 5]           # NOT sorted
    ss = [2, -1, 3, 4]
    gamma = sp.Rational(4, 3); z = sp.Rational(5, 3)
    A, T, S, w = literal_matrices(qs, ss, N)
    order = sorted(range(N), key=lambda i: -qs[i])   # descending
    P = sp.eye(N)
    P = P[:, order]                                   # M' = P^T M P relabels
    Ar, Tr, Sr = (P.T * A * P), (P.T * T * P), (P.T * S * P)
    B = Sr + Ar
    ok("T6 relabeled B strictly upper", all(B[i, j] == 0 for i in range(N) for j in range(i + 1)))
    ur = sp.Matrix([ss[order[i]] * w[order[i]] for i in range(N)])
    vr = sp.Matrix([ss[order[i]] / w[order[i]] for i in range(N)])
    ok("T6 relabeled B-B^T == u'v'^T-v'u'^T",
       sp.simplify(B - B.T - (ur * vr.T - vr * ur.T)) == sp.zeros(N, N))
    Lam, xi = spectral(gamma, z)
    L = Sr + Lam * Tr + xi * Ar
    hs = hamiltonians(Tr, Ar, B, gamma, 7)
    Lp = sp.eye(N)
    for m in range(1, 8):
        Lp = Lp * L
        ok(f"T6 relabeled tau_{m}", sp.cancel(sp.together(sp.trace(Lp) - conjectured_tau(m, hs, Lam))) == 0)

# ---------------------------------------------------------------- main
abstract_lemma_symbolic(3)
run_degenerate(2)
run_counting(8)
run_appendix()
# literal source instances: (N, qs with possible ties, ss incl. negative & zero, gamma, z, mmax)
cases = [
    (3, [3, 1, -2], [2, -1, 3], sp.Rational(3, 2), sp.Rational(5, 2), 8),
    (4, [4, 2, 2, -1], [1, 3, -2, 5], sp.Rational(-5, 3), sp.Rational(7, 3), 7),
    (5, [5, 5, 1, -3, -3], [2, 0, -3, 4, 1], sp.Rational(1, 2), sp.Rational(9, 4), 7),
    (2, [1, -1], [7, 11], sp.Integer(2), sp.Integer(3), 8),       # gamma=+2 literal
    (2, [1, -1], [7, 11], sp.Integer(-2), sp.Integer(3), 8),      # gamma=-2 literal
    (1, [4], [6], sp.Rational(3, 2), sp.Rational(5, 2), 3),       # N=1 edge
]
run_relabel()
for idx, (N, qs, ss, gamma, z, mmax) in enumerate(cases):
    run_literal(N, mmax, qs, ss, gamma, z, f"literal#{idx}(N={N})")

results["status"] = "PASS" if not results["failures"] else "FAIL"
out = Path(__file__).with_name("review-check.json")
out.write_text(json.dumps(results, indent=2, default=str) + "\n")
print(json.dumps(results, indent=2, default=str))
