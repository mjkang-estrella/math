"""Exact refutation of r349 T1 (pointwise iff) and of the T2 mechanism, n = 2.

Basis v = (x^2, xy, y^2). Every claim below is an exact rational / polynomial-identity check.
Exit code 0 iff all assertions hold.
"""
import json
import sys
from fractions import Fraction as F

sys.path.insert(0, __file__.rsplit('/', 1)[0])
from gramlib import quad_monomials, mult_image, nullspace_Q, quartic_monomials

n = 2
v = quad_monomials(n)            # [(2,0),(1,1),(0,2)]
assert v == [(2, 0), (1, 1), (0, 2)]
N = len(v)
pairs = [(a, b) for a in range(N) for b in range(a, N)]
quart = quartic_monomials(n)

# mult as a matrix on the symmetric parameters
def sym_from_params(x):
    G = [[F(0)] * N for _ in range(N)]
    for (a, b), c in zip(pairs, x):
        G[a][b] = c
        G[b][a] = c
    return G

rows = []
for q in quart:
    row = []
    for (a, b) in pairs:
        E = [[0] * N for _ in range(N)]
        E[a][b] = 1
        E[b][a] = 1
        row.append(mult_image(E, n).get(q, 0))
    rows.append(row)
ker = nullspace_Q(rows, len(pairs))
assert len(ker) == 1, len(ker)                       # kappa(2) = 1
K = sym_from_params(ker[0])
scale = K[0][2]
K0 = [[x / scale for x in r] for r in K]
assert K0 == [[0, 0, 1], [0, -2, 0], [1, 0, 0]]      # K0 = E13+E31-2E22
assert mult_image(K0, n) == {}

def restrict(M, idx):
    return [[M[i][j] for j in idx] for i in idx]

def minor2(M, i, j):
    return M[i][i] * M[j][j] - M[i][j] * M[j][i]

out = {}

# Example A: q = (x^2), f = x^4, G0 = e1 e1^T, W = ker G0 = span(e2, e3).
G0 = [[F(1), 0, 0], [0, 0, 0], [0, 0, 0]]
assert mult_image(G0, n) == {(4, 0): 1}
KW = restrict(K0, [1, 2])
assert KW == [[-2, 0], [0, 0]]                       # nonzero, NSD, singular: NOT indefinite
# Fiber is G0 + t K0 (ker mult is 1-dim). Principal minor on {x^2, y^2}:
# det [[1, t], [t, 0]] = -t^2 < 0 for t != 0, so only t = 0 is PSD.
for t in [F(1, 10**6), F(-1, 10**6), F(1), F(-1), F(37, 5)]:
    Gt = [[G0[i][j] + t * K0[i][j] for j in range(N)] for i in range(N)]
    assert minor2(Gt, 0, 2) == -t * t < 0
# symbolic: minor2(G0+tK0,0,2) = 1*0 - t*t identically
out['example_A'] = {
    'q': ['x^2'], 'f': 'x^4', 'W_basis': ['xy', 'y^2'],
    'K0_restricted_to_W': [[-2, 0], [0, 0]],
    'T1_prediction': 'not singleton (K0|W, -K0|W semidefinite, not indefinite)',
    'actual': 'Gram(x^4) = {diag(1,0,0)}: minor {x^2,y^2} of G0+tK0 equals -t^2',
    'refutes': 'T1 direction singleton => all K|W indefinite; and T1 proof step "K|W>=0 => G0+tK PSD for small t" (take K=-K0)'}

# Example B: q = (xy, y^2), f = x^2 y^2 + y^4, G0 = diag(0,1,1), W = span(e1).
G0b = [[F(0), 0, 0], [0, F(1), 0], [0, 0, F(1)]]
assert mult_image(G0b, n) == {(2, 2): 1, (0, 4): 1}
assert restrict(K0, [0]) == [[0]]                    # K0|W = 0, i.e. ker(mult) ∩ L_W != 0
for t in [F(1, 10**6), F(-1, 10**6), F(1, 3), F(-2)]:
    Gt = [[G0b[i][j] + t * K0[i][j] for j in range(N)] for i in range(N)]
    assert minor2(Gt, 0, 2) == -t * t < 0
out['example_B'] = {
    'q': ['xy', 'y^2'], 'f': 'x^2 y^2 + y^4', 'n': 2, 'm': 2, 'w': 1, 'kappa': 1,
    'K0_restricted_to_W': [[0]],
    'T2_claim': 'w(w+1)/2 <= kappa => no m-tuple has singleton spectrahedron (via K|W=0 or PSD restriction)',
    'actual': 'Gram(f) = {diag(0,1,1)}: minor {x^2,y^2} of G0+tK0 equals -t^2',
    'refutes': 'T2 mechanism and T2 statement read pointwise; generic conclusion m(2)=1 is unaffected'}

out['status'] = 'PASS'
print(json.dumps(out, indent=1))
