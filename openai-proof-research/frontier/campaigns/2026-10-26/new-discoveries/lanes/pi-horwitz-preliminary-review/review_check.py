#!/usr/bin/env python3
"""Independent adversarial re-derivation checks for the Horwitz 327618 preliminary review.
Written fresh by the reviewer; not derived from check_proposal.py.
Checks, for n in ranges stated:
  (A) Taylor identity log a - H_m + sum C_j (t/a)^j == Taylor poly of log at a through degree m,
      and contact: d^r/dt^r [log t - (log a - H_m + sum C_j (t/a)^j)]|_{t=a} = 0 for r=0..m.
  (B) Coefficient identity: sum_{k=j}^m binom(k,j)/k = binom(m,j)/j  (hockey-stick form).
  (C) Literal source normal n_hat(t) = (W_1n, -W_2n, ..., (-1)^(n+1) W_nn) equals
      (-1)^(n+1) prod_{j=1}^{m} j! * (-C_1/a, ..., -C_m/a^m, 1).
  (D) Sign identity against the SOURCE IZ definition: (-1)^(n+i) V_i / V == 1/prod_{k!=i}(a_i-a_k)
      with V = prod_{j<i}(a_i-a_j) and V_i the (n-1)x(n-1) Vandermonde (rows 1..a^(n-2)) of the
      remaining columns in increasing index order. Verified symbolically (rational function) for n<=6
      and exactly for random rational nodes n<=10.
  (E) Actual intersection: solve the literal n linear equations (source hyperplanes at nodes) and
      check exp(last coord) == IZ expression, at generic random positive rational nodes, exact arithmetic.
  (F) Mean property: exp(last coord) strictly between min and max node (exact rationals).
"""
import json
import random
from fractions import Fraction
from pathlib import Path

import sympy as sp

t = sp.symbols('t', positive=True)
rows = []
ok = True

# ---------- (A)(B) symbolic Taylor / contact ----------
for n in range(2, 15):
    m = n - 1
    H = sum(sp.Rational(1, k) for k in range(1, m + 1))
    C = {j: (-1)**(j - 1) * sp.binomial(m, j) / j for j in range(1, m + 1)}
    a = sp.symbols('a', positive=True)
    T = sp.log(a) + sum((-1)**(k - 1) * (t - a)**k / (k * a**k) for k in range(1, m + 1))
    P = sp.log(a) - H + sum(C[j] * t**j / a**j for j in range(1, m + 1))
    assert sp.expand(T - P) == 0, f"Taylor identity fails n={n}"
    for r in range(0, m + 1):
        assert sp.simplify(sp.diff(sp.log(t) - P, t, r).subs(t, a)) == 0, f"contact fails n={n} r={r}"
    rows.append({'n': n, 'taylor_identity': 'PASS', 'contact_order': m})
print("A/B: Taylor+contact n=2..14 PASS")

# (B) hockey-stick identity symbolic in m
for m in range(1, 15):
    for j in range(1, m + 1):
        assert sp.simplify(sum(sp.binomial(k, j) / k for k in range(j, m + 1))
                           - sp.binomial(m, j) / j) == 0, f"coeff identity fails m={m} j={j}"
print("B: binom(k,j)/k hockey-stick identity m=1..14 PASS")

# f^(m) identity: d^m/dt^m (t^m log t) = m! (log t + H_m)
for m in range(1, 13):
    assert sp.simplify(sp.diff(t**m * sp.log(t), t, m)
                       - sp.factorial(m) * (sp.log(t) + sp.harmonic(m))) == 0, f"f^(m) fails m={m}"
print("f^(m) = m!(log t + H_m) m=1..12 PASS")

# ---------- (C) literal Wronskian normals, n=2..9 ----------
for n in range(2, 10):
    m = n - 1
    curve = [t**j for j in range(1, m + 1)] + [sp.log(t)]
    D = sp.Matrix([[sp.diff(f, t, r) for f in curve] for r in range(1, n)])  # (n-1) x n
    # literal source convention: n_hat_j = (-1)^(j+1) W_{j,n}, W_{j,n} = det of D without column j (1-indexed)
    n_hat = sp.Matrix([(-1)**(j + 1) * sp.expand(D[:, [c for c in range(n) if c != j - 1]].det())
                       for j in range(1, n + 1)])
    expected = sp.Matrix([(-1)**j * sp.binomial(m, j) / (j * t**j) for j in range(1, m + 1)]
                         + [sp.Integer(1)])
    factor = (-1)**(n + 1) * sp.prod(sp.factorial(j) for j in range(1, n))
    assert sp.simplify(n_hat - factor * expected) == sp.zeros(n, 1), f"normal mismatch n={n}"
print("C: literal source Wronskian normals == factor * expected, n=2..9 PASS")

# ---------- (D) sign identity vs source IZ ----------
def V_src(a_list):
    n = len(a_list)
    p = sp.Integer(1)
    for i in range(n):
        for j in range(i):
            p *= a_list[i] - a_list[j]
    return p

def Vi_src(a_list, i):
    n = len(a_list)
    rem = [a_list[k] for k in range(n) if k != i]
    M = sp.Matrix([[r**p for r in rem] for p in range(n - 1)])
    return sp.expand(M.det())

# symbolic rational-function identity, n=3..6
for n in range(3, 7):
    avars = sp.symbols(f'x1:{n+1}')
    lhs = sp.together(sum(((-1)**(n + i + 1) * avars[i]**(n - 1) * Vi_src(avars, i) * sp.log(avars[i])
                           / V_src(avars) for i in range(n))))
    rhs = sum(avars[i]**(n - 1) * sp.log(avars[i]) / sp.prod(avars[i] - avars[k]
              for k in range(n) if k != i) for i in range(n))
    # compare after cancelling the log-free prefactors: multiply both by exp-free test: check weights only
    w_lhs = sp.together(sum(((-1)**(n + i + 1) * Vi_src(avars, i) for i in range(n)), sp.Integer(0)) / V_src(avars))
    w_rhs = sum(1 / sp.prod(avars[i] - avars[k] for k in range(n) if k != i) for i in range(n))
    # per-term identity:
    for i in range(n):
        assert sp.simplify(sp.together(((-1)**(n + i + 1) * Vi_src(avars, i) / V_src(avars))
                            - 1 / sp.prod(avars[i] - avars[k] for k in range(n) if k != i))) == 0, \
            f"sign identity fails n={n} i={i}"
print("D: per-term sign identity (-1)^(n+i) V_i/V = 1/prod(a_i-a_k), source V_i convention, n=3..6 PASS (symbolic)")

# exact-rational spot check of the sign identity n=7..10
for n in range(7, 11):
    random.seed(42 + n)
    nodes = [sp.Rational(random.randint(1, 500), random.randint(1, 500) + 1) for _ in range(n)]
    nodes = list(dict.fromkeys(nodes))
    while len(nodes) < n:
        nodes.append(sp.Rational(random.randint(1, 999), 1000))
    for i in range(n):
        lhs = (-1)**(n + i + 1) * Vi_src(nodes, i) / V_src(nodes)
        rhs = 1 / sp.prod(nodes[i] - nodes[k] for k in range(n) if k != i)
        assert sp.simplify(lhs - rhs) == 0, f"sign identity numeric fails n={n} i={i}"
print("D: sign identity exact-rational n=7..10 PASS")

# ---------- (E)(F) actual intersection via literal source hyperplanes, generic nodes ----------
def check_instance(n, nodes):
    m = n - 1
    H = sum(sp.Rational(1, k) for k in range(1, m + 1))
    C = {j: (-1)**(j - 1) * sp.binomial(m, j) / j for j in range(1, m + 1)}
    # source hyperplane at a: n_hat(a) . x = n_hat(a) . alpha(a)
    curve = [t**j for j in range(1, m + 1)] + [sp.log(t)]
    D = sp.Matrix([[sp.diff(f, t, r) for f in curve] for r in range(1, n)])
    n_hat_t = [(-1)**(j + 1) * sp.expand(D[:, [c for c in range(n) if c != j - 1]].det())
               for j in range(1, n + 1)]
    A, rhs = [], []
    for a_i in nodes:
        row = [sp.simplify(nh.subs(t, a_i)) for nh in n_hat_t]
        A.append(row)
        rhs.append(sum(curve[c].subs(t, a_i) * row[c] for c in range(n)))
    A = sp.Matrix(A); rhs = sp.Matrix(rhs)
    P = A.inv() * rhs  # exact rational solve (rows rational in nodes)
    z = P[-1]
    iz_log = sum(nodes[i]**(n - 1) * sp.log(nodes[i]) /
                 sp.prod(nodes[i] - nodes[k] for k in range(n) if k != i) for i in range(n)) - H
    assert sp.simplify(z - iz_log) == 0, f"intersection last coord != IZ log, n={n}"
    # mean property: z strictly between log min and log max  <=>  exp(z) in (min,max)
    assert z > sp.log(min(nodes)) and z < sp.log(max(nodes)), f"internality fails n={n}"
    # also verify each solved coordinate satisfies ALL literal source plane equations
    assert all(sp.simplify(sum(A[r, c] * P[c] for c in range(n)) - rhs[r]) == 0 for r in range(n))
    return True

for n in range(2, 10):
    random.seed(1000 + n)
    seen = set()
    nodes = []
    while len(nodes) < n:
        r = sp.Rational(random.randint(1, 2000), random.randint(1, 2000))
        if r > 0 and r not in seen:
            seen.add(r); nodes.append(r)
    check_instance(n, nodes)
print("E/F: literal source-plane intersections == IZ, exact, generic rational nodes, n=2..9 PASS")

out = {'status': 'PASS: independent re-derivation finite/symbolic evidence only; not a formal certificate',
       'independent': True,
       'checks': {
           'taylor_contact_n2_14': 'PASS',
           'hockey_stick_coeff_identity_m1_14': 'PASS',
           'f^(m)_identity_m1_12': 'PASS',
           'literal_wronskian_normals_n2_9': 'PASS',
           'source_IZ_sign_identity_symbolic_n3_6_and_exact_n7_10': 'PASS',
           'generic_node_intersection_equals_IZ_n2_9': 'PASS',
           'internality_n2_9': 'PASS'}}
Path(Path(__file__).with_name('review_checks.json')).write_text(json.dumps(out, indent=2) + '\n')
print(json.dumps(out, indent=2))
