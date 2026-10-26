"""Independent review check: exact + numerical, different code path from parent.

Path: build each difference matrix explicitly as a 2x2 complex matrix,
compute cos(M) = (exp(iM)+exp(-iM))/2 via *eigendecomposition* (different from
parent's floating eig check and from Lean's series/intertwining), verify each
cosine table entry, then the quadratic form with exact rational/symbolic c.
"""
import numpy as np
import sympy as sp

pi = sp.pi
s15 = sp.sqrt(15)

# plane(a,b) = [[a, b],[b, -a]]  (real symmetric Pauli-type)
def plane(a, b):
    return sp.Matrix([[a, b], [b, -a]])

Z = sp.Matrix([[1, 0], [0, -1]])
S = sp.Matrix([[0, 1], [1, 0]])

U = plane(2*pi, 0)            # = 2*pi*Z
V = plane(-7*pi/4, pi*s15/4)  # = pi*(-7*Z + sqrt(15)*S)/4

assert sp.simplify(U - 2*pi*Z) == sp.zeros(2)
assert sp.simplify(V - pi*(-7*Z + s15*S)/4) == sp.zeros(2)

# squares
for name, M, val in [("U^2", U*U, 4*pi**2*sp.eye(2)),
                     ("V^2", V*V, 4*pi**2*sp.eye(2)),
                     ("(U+V)^2", (U+V)*(U+V), pi**2*sp.eye(2)),
                     ("(U-V)^2", (U-V)*(U-V), 15*pi**2*sp.eye(2))]:
    d = sp.simplify(M - val)
    assert d == sp.zeros(2), name
    print(f"exact OK: {name} = {sp.simplify((M)[0,0])} * I")

# cos of M with M^2 = r^2 I via eigendecomposition, exact: eigenvalues +-r
# Verify: cos(M) = cos(r) I exactly. Independent route: minimal polynomial.
# cos(M) is the function calc; for M^2=r^2 I, M is a root of x^2-r^2,
# f(M) = a M + b I with f(x)=cos x on spectrum: a*±r + b = cos(±r) => a=0, b=cos r.
# Numerical confirmation via dense eigendecomposition of exp(iM):
def cosM(M):
    Mf = np.array(M.evalf(), dtype=complex)
    w, Q = np.linalg.eigh(Mf)   # M is Hermitian
    return Q @ np.diag(np.cos(w)) @ Q.conj().T

I2 = sp.eye(2)
c = sp.cos(pi*s15)
t = (1 + c)/2

pts = [sp.zeros(2), U, U+V, V]
def canon(M):
    M = sp.simplify(M)
    for cand, key in [(sp.zeros(2), '0'), (U, 'U'), (V, 'V'), (U+V, 'UV'), (U-V, 'UD')]:
        if sp.simplify(M - cand) == sp.zeros(2): return key
        if sp.simplify(M + cand) == sp.zeros(2): return key
    raise ValueError
vals = {'0': 1, 'U': 1, 'V': 1, 'UV': -1, 'UD': c}
table = {}
for i in range(4):
    for j in range(4):
        table[(i,j)] = vals[canon(pts[i]-pts[j])]
pts = [sp.zeros(2), U, U+V, V]
for i in range(4):
    for j in range(4):
        D = pts[i] - pts[j]
        C = cosM(D)
        expected = sp.Matrix(table[(i,j)] * I2)
        err = np.abs(np.array((sp.simplify(C - expected)).evalf(), dtype=complex)).max()
        # exact: D^2 = (a^2+b^2) I with r^2 matched exactly (checked above per plane);
        # lemma: M^2=r^2 I, r>0  =>  cos M = cos r I  (intertwining by rI+-M).
        # high-precision numeric confirmation of the lemma application:
        Df = np.array(D.evalf(50), dtype=complex)
        wv, Qv = np.linalg.eigh(Df)
        Cv = Qv @ np.diag(np.cos(wv)) @ Qv.conj().T
        rf = float(sp.sqrt((D**2)[0,0].evalf(50)))
        assert np.abs(Cv - np.cos(rf)*np.eye(2)).max() < 1e-12, (i,j)
        # and D^2 exactly scalar:
        assert sp.simplify(D*D - (D*D)[0,0]*sp.eye(2)) == sp.zeros(2)
        err = np.abs(Cv - np.array(expected.evalf(50), dtype=complex)).max()
        assert err < 1e-12, f"num fail ({i},{j}) {err}"
print("exact + numeric OK: all 16 cos(point_i - point_j) match table")

# uncentered kernel (first coord) and quadratic form
K = sp.Matrix(4, 4, lambda i, j: (1 + table[(i,j)])/2)
Ks = K - sp.Rational(1,4)*sp.ones(4,4)
y = sp.Matrix([1, -1, 1, -1])
q = (y.T * Ks * y)[0, 0]
q_expr = sp.simplify(q)
assert sp.simplify(q_expr - (c - 3)) == 0, q_expr
print("quadratic form (centered, exact) =", q_expr, "=", q_expr.evalf())
assert q_expr.evalf() < -2
# uncentered also negative:
q0 = (y.T * K * y)[0,0]
print("uncentered form =", sp.simplify(q0), "=", q0.evalf())
assert sp.simplify(q0 - (c - 3)) == 0  # J-term vanishes on y since sum y_i = 0
assert q0.evalf() < -2
# full 8x8 literal matrix: entry ((i,a),(j,b)) = beta_ij * delta_ab  =>  B kron I2
# where B[i,j] = sourceBlock scalar coefficient (all entries central).
# NOTE: a first attempt here used M8[a,b]=Ks[a%4,b%4] (wrong flattening); corrected.
B = sp.Matrix(4, 4, lambda i, j: Ks[i, j])
M8 = sp.kronecker_product(B, sp.eye(2))
M8e = np.array(M8.evalf(), dtype=complex)
w = np.linalg.eigvalsh(M8e)
print("8x8 (= B (x) I2) eigenvalues:", w)
assert w.min() < 0
w4 = np.linalg.eigvalsh(np.array(B.evalf(), dtype=complex))
print("4x4 block eigenvalues (each x2 in 8x8):", w4)
assert np.allclose(np.sort(np.repeat(w4, 2)), np.sort(w), atol=1e-10)
# Rayleigh quotient of the literal witness y (x) e1 on the correct 8x8
# (index (i,a) -> 4*i + a, so y (x) e1 = [y0,0,y1,0,y2,0,y3,0]):
wi = sp.Matrix([y[0],0,y[1],0,y[2],0,y[3],0])
qv = (wi.T * M8 * wi)[0,0]
assert sp.simplify(qv - (c - 3)) == 0, qv
print("witness quadratic form on literal 8x8 =", sp.simplify(qv), "=", qv.evalf())
assert qv.evalf() < 0
print("min eig < 0, Hermitian by construction (real symmetric)")
# t value
print("c = cos(pi*sqrt(15)) =", c.evalf(20))
print("t = (1+c)/2 =", t.evalf(20))
