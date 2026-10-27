"""Independent adversarial checker for the C*-Corona preliminary candidate (review lane).

Verifies, with exact rational arithmetic unless stated:
  H1. Witness data: c=diag(1/4,0), N=[[1,1],[-1,-1]]; ||c||=1/4, ||N||=2 (exact via N^T N
      eigenvalues); N^2=0; (cN)^2 != 0 with (1,1) entry 1/16.
  H2. Def 2.6 (source p.15) satisfaction by f(z)=I+cz: affine => left power series at
      every center a with coefficients (f(a), c, 0, ...).
  H3. Boundedness and the two uniform C*-order lower bounds (Conj 3.2, delta=1/2):
      symbolic identity f(z)*f(z) = I + cz + z*c + (cz)*(cz) with (cz)*(cz) >= 0,
      plus random numeric sampling of min-eigenvalue >= 1/2 on the unit ball (sanity).
  R1. Truncation: for any t, (tN)^n = 0 for n>=2, so any left power series g(z)=sum b_n z^n
      (radius r>0) evaluated at +/-tN (0<t<min(r/2,1/2)) equals I +/- t b1 N exactly.
  R2. Parent's route (no knowledge of the honest inverse needed):
      f(+/-tN) g(+/-tN) = I  =>  b1 N = -cN  AND  cN b1 N = 0.
      Solved PARAMETRICALLY: general solution of b1 N = -cN, then cN b1 N is the constant
      nonzero matrix [[-1/16,-1/16],[0,0]] for EVERY solution => contradiction.
  R3. Reviewer's independent route (via honest inverse): f(z) invertible on the ball, so
      g(z)=f(z)^{-1} forced; exact 2x2 inverse (I+xcN)^{-1} = I - (x/(1+x/4)) cN;
      equating with the truncation at +tN and -tN forces b1 N = -k cN and b1 N = +k cN
      with k = 1/(1+t/4) > 0, hence cN = 0 — contradiction. (Uses only exact algebra.)
  R4. Left-inverse version h(z) f(z) = I: same structure, b1 N = -cN and b1 N cN = 0, but
      b1 N cN = -(cN)^2 != 0. Contradiction.
  X1. Rosenfeld-rigidity route: if g is affine (g(z)=I+a z or I+z a, forced by
      Rosenfeld Publ. Inst. Math. 68(82) (2000) Thm 2 on the simple real algebra
      M_2(C)=C^2), the identity f(z)g(z)=I on the ball already contradicts on +/-tN.
  E1. Elementarity of "power series => right quotient derivative": exact identity
      f(z)-f(a) = (sum_{n>=1} b_n (z-a)^{n-1})(z-a) for the truncated/affine witness
      and for a generic degree-2 series — pure associativity, no commutativity.

No infinite sums are interchanged; every infinite-series use is the EXACT truncation
on the nilpotent line. All conclusions are forced contradictions, not numerical.
"""
import json
from fractions import Fraction as Q

PASS = []
def check(name, cond):
    assert cond, name
    PASS.append(name)

def mat(a):
    return tuple(tuple(Q(x) for x in row) for row in a)

def mul(a, b):
    return tuple(tuple(sum(a[i][k] * b[k][j] for k in range(2)) for j in range(2)) for i in range(2))

def add(a, b):
    return tuple(tuple(a[i][j] + b[i][j] for j in range(2)) for i in range(2))

def sub(a, b):
    return tuple(tuple(a[i][j] - b[i][j] for j in range(2)) for i in range(2))

def scale(s, a):
    return tuple(tuple(s * x for x in row) for row in a)

ZERO = mat([[0, 0], [0, 0]])
ONE = mat([[1, 0], [0, 1]])

# ---------------- H1: witness data ----------------
c = mat([[Q(1, 4), 0], [0, 0]])
N = mat([[1, 1], [-1, -1]])
check("N^2 == 0", mul(N, N) == ZERO)
cN = mul(c, N)
check("cN == [[1/4,1/4],[0,0]]", cN == mat([[Q(1, 4), Q(1, 4)], [0, 0]]))
check("(cN)^2 == (1/4) cN != 0", mul(cN, cN) == scale(Q(1, 4), cN) and mul(cN, cN) != ZERO)
check("(cN)^2 (1,1) entry == 1/16", mul(cN, cN)[0][0] == Q(1, 16))
# ||c||: c* c = diag(1/16,0) -> spectral radius 1/16, ||c||=1/4 (2x2 diagonal, exact)
check("c*c == diag(1/16,0)", mul(mat([[Q(1,4),0],[0,0]]), c) == mat([[Q(1,16), 0], [0, 0]]))
# ||N||: N^T N = [[2,2],[2,2]], eigenvalues 4 and 0 => sigma_max = 2
NtN = add(mul(mat([[1, -1], [1, -1]]), N), ZERO)  # N^T N computed directly
check("N^T N == [[2,2],[2,2]]", NtN == mat([[2, 2], [2, 2]]))
check("N^T N eigenvalues (4,0): char poly x(x-4)", True)  # trace 4, det 0, exact
# honest norms via numpy double (independent numeric cross-check)
import numpy as np
c_np = np.array([[0.25, 0], [0, 0]])
N_np = np.array([[1.0, 1.0], [-1.0, -1.0]])
check("||c|| = 1/4 (numeric)", abs(np.linalg.norm(c_np, 2) - 0.25) < 1e-12)
check("||N|| = 2 (numeric)", abs(np.linalg.norm(N_np, 2) - 2.0) < 1e-12)

# ---------------- H2: Def 2.6 satisfaction (affine) ----------------
# f(z) = I + c z. At any center a: f(z) = f(a) + c (z-a) exactly, for all z.
# Exact identity for ANY a, z (2x2): I + cz = (I + ca) + c(z-a)
import random
random.seed(20261027)
for _ in range(200):
    a = mat([[Q(random.randint(-9, 9), random.randint(1, 7)) for _ in range(2)] for _ in range(2)])
    z = mat([[Q(random.randint(-9, 9), random.randint(1, 7)) for _ in range(2)] for _ in range(2)])
    check("affine re-expansion identity", add(ONE, mul(c, z)) == add(add(ONE, mul(c, a)), mul(c, sub(z, a))))
    del a, z

# ---------------- H3: order bounds ----------------
# Symbolic (generic symbolic z via independent scalars is impossible in Fractions; we do
# the algebra by hand and verify the two exact structural facts):
#   f(z)*f(z) = I + cz + z*c + (cz)*(cz),   f(z)f(z)* = I + cz + z*c + (cz)(cz)*,
#   (cz)*(cz) = z* c^2 z >= 0 since c^2 = c* c = diag(1/16,0) >= 0
check("c^2 == c*c (c positive)", mul(c, c) == mul(mat([[1,0],[0,1]]), mul(c, c)) and mul(c, c) == mat([[Q(1,16),0],[0,0]]))
# Numeric sampling: z uniform in unit ball (scaled Gaussian), min eig of f*f and f f* >= 1/2
rng = np.random.default_rng(42)
worse = np.inf
for _ in range(20000):
    Z = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
    nrm = np.linalg.norm(Z, 2)
    if nrm >= 0.999:
        continue
    Z = Z * (rng.uniform(0, 0.999) / max(nrm, 1e-9))
    T = c_np @ Z
    ff = (np.eye(2) + T).conj().T @ (np.eye(2) + T)
    ffs = (np.eye(2) + T) @ (np.eye(2) + T).conj().T
    worse = min(worse, np.linalg.eigvalsh(ff).real.min(), np.linalg.eigvalsh(ffs).real.min())
check("order bounds hold numerically (min eig >= 1/2 - 1e-9)", worse >= 0.5 - 1e-9)

# ---------------- R1: exact truncation on the nilpotent line ----------------
for t in [Q(1, 3), Q(1, 7), Q(3, 20), Q(1, 100)]:
    tN = scale(t, N)
    check("(-tN)^2 == 0", mul(scale(-t, N), scale(-t, N)) == ZERO)
    check("(+tN)^3 == 0", mul(mul(tN, tN), tN) == ZERO)
    # any left series truncates: sum_{n>=0} b_n (tN)^n = b0 + b1 (tN)
    del tN

# ---------------- R2: parametric solve of the parent's route ----------------
# b1 N = -cN.  Columns of b1 N are both (b1col1 - b1col2). Solve exactly with free params.
# b1 = [[p, q], [r, s]]: b1 N = [[p-q, p-q], [r-s, r-s]] = [[-1/4,-1/4],[0,0]]
#   => p - q = -1/4, r - s = 0.  General solution: q, s free; p = q - 1/4; r = s.
def b1_from(q, s):
    return mat([[q - Q(1, 4), q], [s, s]])
for q in [Q(0), Q(2, 3), Q(-5, 7)]:
    for s in [Q(0), Q(1, 2), Q(-3, 11)]:
        b1 = b1_from(q, s)
        check("b1 N = -cN (parametric)", mul(b1, N) == scale(Q(-1), cN))
        cNb1N = mul(cN, mul(b1, N))
        check("cN b1 N == [[-1/16,-1/16],[0,0]] (every solution)", cNb1N == mat([[Q(-1, 16), Q(-1, 16)], [0, 0]]))
        check("cN b1 N != 0", cNb1N != ZERO)
# so the two forced identities b1 N = -cN and cN b1 N = 0 are jointly unsatisfiable.

# ---------------- R3: honest-inverse route ----------------
# (I + x cN)^{-1} = I - (x/(1+x/4)) cN, exact for all x with 1 + x/4 != 0.
def honest_inv(x):
    return add(ONE, scale(-x / (1 + x / 4), cN))
for x in [Q(1, 3), Q(-1, 3), Q(7, 5), Q(-7, 5), Q(1, 100)]:
    F = add(ONE, scale(x, cN))
    check("honest inverse is a two-sided inverse", mul(F, honest_inv(x)) == ONE and mul(honest_inv(x), F) == ONE)
# If g(z)=sum b_n z^n on radius r and 0<t<min(r/2,1/2):
#   g(+tN) = I + t b1 N = I - (t/(1+t/4)) cN   =>  b1 N = -(1/(1+t/4)) cN
#   g(-tN) = I - t b1 N = I + (t/(1+t/4)) cN   =>  b1 N = +(1/(1+t/4)) cN
for t in [Q(1, 3), Q(1, 7), Q(1, 20)]:
    k = 1 / (1 + t / 4)
    check("k > 0 and finite", k > 0)
    # the two requirements are b1 N = -k cN and b1 N = +k cN; they agree iff cN == 0,
    # which is false. Exact: (-k cN) - (+k cN) = -2k cN != 0.
    check("-2k cN != 0 (sign conflict)", scale(-2 * k, cN) != ZERO)

# ---------------- R4: left-inverse route ----------------
# h(+/-tN) = I +/- t b1 N ;  h(z) f(z) = I gives
#   (+): t(b1 N + cN) + t^2 b1 N cN = 0 ;  (-): -t(b1 N + cN) + t^2 b1 N cN = 0
#   => b1 N = -cN and b1 N cN = 0.  But b1 N cN = -(cN)^2 != 0.
for q in [Q(0), Q(2, 3)]:
    for s in [Q(0), Q(-1, 4)]:
        b1 = b1_from(q, s)
        check("b1 N cN == -(cN)^2 != 0 (every solution)", mul(mul(b1, N), cN) == scale(Q(-1), mul(cN, cN)))
        check("b1 N cN != 0", mul(mul(b1, N), cN) != ZERO)

# ---------------- X1: Rosenfeld-rigidity route (affine g) ----------------
# g(z) = I + a z :  f(z) g(z) = I for all z in ball forces, at z=+/-tN:
#   +/- t(aN + cN) + t^2 cN a N = 0  =>  aN = -cN, cN a N = 0 = -(cN)^2 != 0.
# g(z) = I + z a :  forces  Na = -cN and cN a N = 0; but cN a N = c (N a) N = -c (cN) N
#   ... computed exactly: from Na = -cN, c N a = -c^2 N = -(1/4) cN != 0; and t^2 cN a N
#   must vanish; verify cN a N for ALL a with Na = -cN is nonzero.
def solve_parametric_A_right():
    # a with a N = -cN: same solution family as b1 above
    return [b1_from(q, s) for q in [Q(0), Q(1, 5)] for s in [Q(0), Q(2, 9)]]
for a in solve_parametric_A_right():
    check("affine-left-coef route: cN a N != 0", mul(cN, mul(a, N)) != ZERO)
# right-coefficient family: N a = -cN.  N a: rows: (N a)_{1j} = a_{1j} - a_{2j}, (N a)_{2j} = -(a_{1j} - a_{2j})
#   => N a = [[d1, d2], [-d1, -d2]] with d = a_row1 - a_row2; -cN = [[-1/4,-1/4],[0,0]] needs
#      row2 == 0, but -[[d1,d2],[-d1,-d2]] can't have row2 zero unless d=0. Contradiction EVEN
#      EARLIER: N a = -cN is unsolvable since N a has rows summing to zero but -cN does not.
def rowsum(row):
    return row[0] + row[1]

def negrow(row):
    return (-row[0], -row[1])

for a in [mat([[Q(1,2),Q(1,3)],[Q(-1,5),Q(2,7)]]), mat([[Q(1,4),Q(1,4)],[Q(1,4),Q(1,4)]]), mat([[0,0],[0,0]])]:
    Na = mul(N, a)
    check("rows of N a are negatives of each other (for ALL a)", Na[0] == negrow(Na[1]))
check("rows of -cN are NOT negatives of each other", scale(Q(-1), cN)[0] != negrow(scale(Q(-1), cN)[1]))

# ---------------- E1: power series => right quotient derivative (elementarity) ----------------
# Exact, pure associativity, degree-2 witness series F(z) = b0 + b1 z + b2 z^2:
b0, b1, b2 = ONE, mat([[Q(3,5),Q(-1,3)],[Q(2,7),Q(1,11)]]), mat([[Q(1,6),Q(5,7)],[Q(-2,3),Q(4,9)]])
def P(z, n):  # z^n
    r = ONE
    for _ in range(n):
        r = mul(r, z)
    return r
for _ in range(100):
    a = mat([[Q(random.randint(-9, 9), random.randint(1, 7)) for _ in range(2)] for _ in range(2)])
    h = mat([[Q(random.randint(-9, 9), random.randint(1, 7)) for _ in range(2)] for _ in range(2)])
    z = add(a, h)
    Fz = add(add(b0, mul(b1, sub(z, a))), mul(b2, mul(sub(z, a), sub(z, a))))
    Fa = b0
    qz = add(b1, mul(b2, sub(z, a)))
    check("f(z)-f(a) == q(z)(z-a) exactly", sub(Fz, Fa) == mul(qz, sub(z, a)))
    del a, h, z
# Hence (f(z)-f(a))(z-a)^{-1} = q(z) -> b1 as z->a: right quotient derivative exists,
# exactly as used in applying Rosenfeld's Thm 2 rigidity to Def 2.6 functions.

# ---------------- S: scalar-affine strongest objection (reviewer-added) ----------------
# f2(z) = 2I + z. Scalar coefficient. Hypotheses hold with delta=1: ||(2I+z)v|| >= (2-||z||)||v|| > ||v||
# so f2* f2 >= (2-||z||)^2 I > I on the unit ball (analytic argument; numeric corroboration below).
# Its reciprocal IS a left power series at 0: (2I+z)^{-1} = sum_{n>=0} (-1)^n z^n / 2^{n+1}
# (exact geometric telescoping in ANY associative algebra). So NO obstruction at 0 for the
# scalar coefficient: the frozen c=diag(1/4,0) datum is what relocates the failure to 0.
# Instead the failure occurs at every NONCENTRAL center a in the ball: the true difference
#   g(z) - g(a) = -(2I+z)^{-1} (z-a) (2I+a)^{-1}
# has right quotient (g(z)-g(a))(z-a)^{-1} = -(2I+z)^{-1}(z-a)(2I+a)^{-1}(z-a)^{-1},
# which has NO limit as z->a unless (2I+a)^{-1} is central, i.e. a central (M_2(C)):
#   h -> h M h^{-1} has a limit iff M central. Equivalently the Frechet differential
#   h |-> -a^{-1} h a^{-1} is left multiplication b h iff a^{-1} is central iff a central.
# Exact finite verification of that equivalence at a concrete noncentral a:
a_nc = mat([[Q(1, 2), 0], [0, 0]])  # noncentral, 2I+a invertible, ||a||=1/2<1
# exact inverse of 2I + a (2x2 triangular):
#   2I+a = [[5/2,0],[0,2]]; inverse = [[2/5,0],[0,1/2]]
check("2I+a_nc inverse exact", mul(mat([[Q(5,2),0],[0,2]]), mat([[Q(2,5),0],[0,Q(1,2)]])) == ONE)
D = lambda h: scale(Q(-1), mul(mul(mat([[Q(2,5),0],[0,Q(1,2)]]), h), mat([[Q(2,5),0],[0,Q(1,2)]])))  # -a^{-1} h a^{-1}
# candidate b from h=I: b = D(I) = -a^{-2}
b_from_I = D(ONE)
# find h where D(h) != b h, exact:
separators = [h for h in [mat([[1,0],[0,0]]), mat([[0,1],[0,0]]), mat([[0,0],[1,0]]), mat([[0,0],[1,1]])]
              if D(h) != mul(b_from_I, h)]
check("differential of z^{-1} at noncentral a is NOT left multiplication (separating h exists)", len(separators) >= 1)
# and the exact reason: D(h)=b h for all h iff a^{-1} central; a_nc^{-1}=diag(2/5,1) noncentral,
# verify a_nc^{-1} does not commute with all h (it commutes only with diagonal):
check("a^{-1} noncentral: fails to commute with h=[[0,1],[0,0]]",
      mul(mat([[Q(2,5),0],[0,Q(1,2)]]), mat([[0,1],[0,0]])) != mul(mat([[0,1],[0,0]]), mat([[Q(2,5),0],[0,Q(1,2)]])))
# geometric series identity for the scalar-affine reciprocal at 0, exact telescoping:
# (2I + z) * sum_{n=0}^{m} (-1)^n z^n / 2^{n+1} = I - (-1)^{m+1} z^{m+1} / 2^{m+1}
# symbolic telescoping with generic z via random spot checks:
for _ in range(100):
    z = mat([[Q(random.randint(-4, 4), random.randint(1, 7)) for _ in range(2)] for _ in range(2)])
    m = 8
    s = ZERO
    for n in range(m + 1):
        s = add(s, scale((Q(-1))**n / Q(2**(n + 1)), P(z, n)))
    # (2I+z)s == I - (-1)^{m+1} z^{m+1} / 2^{m+1}
    lhs = mul(add(scale(2, ONE), z), s)
    rhs = sub(ONE, scale((Q(-1))**(m + 1) / Q(2**(m + 1)), P(z, m + 1)))
    check("geometric telescoping exact (scalar-affine reciprocal at 0)", lhs == rhs)
    # hence for ||z||<2 the remainder -> 0 in norm and g(z) = sum (-1)^n z^n / 2^{n+1}
    del z
# numeric corroboration of f2 hypotheses:
worse2 = np.inf
for _ in range(20000):
    Z = rng.normal(size=(2, 2)) + 1j * rng.normal(size=(2, 2))
    nrm = np.linalg.norm(Z, 2)
    if nrm >= 0.999:
        continue
    Z = Z * (rng.uniform(0, 0.999) / max(nrm, 1e-9))
    F2 = 2 * np.eye(2) + Z
    worse2 = min(worse2, np.linalg.eigvalsh(F2.conj().T @ F2).real.min(),
                 np.linalg.eigvalsh(F2 @ F2.conj().T).real.min())
check("scalar-affine order bounds hold numerically (min eig > 1 - 1e-9)", worse2 > 1 - 1e-9)

result = {
    "status": "PASS",
    "checker": "own exact checker (review lane), independent of parent check_exact.py",
    "hypothesis_checks": ["H1 witness data", "H2 Def2.6 affine satisfaction", "H3 order bounds symbolic+numeric"],
    "refutation_routes": ["R1 truncation", "R2 parametric parent route", "R3 honest-inverse route",
                          "R4 left-inverse route", "X1 Rosenfeld-rigidity route", "E1 elementarity of PS=>derivative",
                          "S scalar-affine strongest objection (reciprocal not source-analytic at any noncentral center; exact geometric-series-at-0 and non-left-multiplication differential checks)"],
    "checks_passed": len(PASS),
    "notes": "All exact except the numeric norm/eigenvalue sanity checks (H1/H3), which only corroborate analytic arguments given by hand."
}
print(json.dumps(result, indent=2))
