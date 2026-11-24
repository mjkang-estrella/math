"""Exact Gaussian-integer matrix identities; not validation of upstream theorems."""
import json

def adj(a):
    return [[a[j][i].conjugate() for j in range(len(a))] for i in range(len(a[0]))]
def mul(a, b):
    return [[sum(x*y for x, y in zip(row, col)) for col in zip(*b)] for row in a]
def sub(a, b):
    return [[x-y for x, y in zip(r, s)] for r, s in zip(a, b)]
def tr(a):
    return sum(a[i][i] for i in range(len(a)))
def norm2(a):
    return sum((x.conjugate()*x).real for row in a for x in row)
def kron(a, b):
    return [[x*y for x in row for y in brow] for row in a for brow in b]
def vec(a):
    return [[x] for row in a for x in row]

# All values are Gaussian integers small enough for exact binary representation.
X = [[1+1j, 2], [0, 1j], [2-1j, -1], [1, 0]]
Y = [[0, 1-1j], [1, -2j], [1j, 2], [-1, 1]]
Z = [[1, 1j, 0, 2], [0, 1, 1j, -1], [1j, 0, 1, 1]]
H = mul(adj(Z), Z)
D = sub(mul(X, adj(X)), mul(Y, adj(Y)))
DX, DY, cross = mul(mul(adj(X), H), X), mul(mul(adj(Y), H), Y), mul(mul(adj(Y), H), X)
assert tr(mul(mul(mul(H, D), H), D)) == norm2(DX)+norm2(DY)-2*norm2(cross)

B = [[0, 1j, 1, 0], [0, 0, 2, 1], [0, 0, 0, -1j], [1, 0, 0, 0]]
C = [[1j, 2], [1-1j, -1]]
lhs = mul(mul(adj(vec(Y)), kron(B, C)), vec(X))[0][0]
base = mul(mul(adj(Y), B), X)
rhs = sum(base[i][j]*C[i][j] for i in range(2) for j in range(2))
assert lhs == rhs

N = [[0, 2], [0, 0]]
I = [[1, 0], [0, 1]]
C0, C1 = [[0, 0], [1, 0]], [[0, 1], [0, 0]]
P0, P1 = kron(I, C0), kron(N, C1)
P = [[x+y for x, y in zip(r, s)] for r, s in zip(P0, P1)]
gram = mul(adj(P), P)
assert gram == [[1, 0, 0, 0], [0, 0, 0, 0], [0, 0, 1, 0], [0, 0, 0, 4]]
top = [[0], [0], [0], [1]]
assert norm2(mul(P, top)) == 4
assert norm2(mul(mul(P, P), top)) == 4

# The corank-one isotropic inequality permits only rank pair (1,1).
admissible = []
for d in range(2, 5):
    pairs = [(p, q) for p in range(1, d) for q in range(1, d)
             if p+q <= d and d-1 <= d-max(p, q)]
    assert pairs == [(1, 1)]
    admissible.append({"dimension": d, "rank_pairs": pairs})
print(json.dumps({"passed": True, "checks": ["block trace identity", "complex base-first bilinear pairing", "weighted-shift example", "corank-one inertia bounds"],
                  "admissible": admissible,
                  "scope": "Exact finite identities only; no numerical evidence is used as a proof."}, indent=2))
