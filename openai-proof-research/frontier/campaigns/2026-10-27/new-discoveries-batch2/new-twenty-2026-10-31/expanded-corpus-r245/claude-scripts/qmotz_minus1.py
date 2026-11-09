"""Integer certificate at q = -1 for MathDB 339077 (three-shift, n = 5): M_k(-1), the 5x5 Hankel matrix
[M_{i+j+3}(-1)], its determinant by exact Fraction elimination and by Leibniz expansion, and t_5(-1).
Also records the same for n = 11 (next failing case) by Fraction elimination."""
import itertools
import json
from fractions import Fraction


def motzkin_at(q, N):
    M = [1]
    for n in range(N):
        M.append(M[n] + sum(q ** (r + 1) * M[r] * M[n - r - 1] for r in range(n)))
    return M


def det_frac(A):
    A = [[Fraction(x) for x in row] for row in A]
    n = len(A)
    d = Fraction(1)
    for k in range(n):
        p = next((i for i in range(k, n) if A[i][k] != 0), None)
        if p is None:
            return 0
        if p != k:
            A[k], A[p] = A[p], A[k]
            d = -d
        d *= A[k][k]
        for i in range(k + 1, n):
            f = A[i][k] / A[k][k]
            for j in range(k, n):
                A[i][j] -= f * A[k][j]
    return d


def det_leibniz(A):
    n = len(A)
    tot = 0
    for perm in itertools.permutations(range(n)):
        inv = sum(1 for i in range(n) for j in range(i + 1, n) if perm[i] > perm[j])
        p = 1
        for i in range(n):
            p *= A[i][perm[i]]
        tot += -p if inv % 2 else p
    return tot


M = motzkin_at(-1, 30)
print('M_k(-1), k=0..15:', M[:16])
H5 = [[M[i + j + 3] for j in range(5)] for i in range(5)]
print('H5(-1) =', json.dumps(H5))
print('det (Fraction) =', det_frac(H5), ' det (Leibniz) =', det_leibniz(H5))
print('t_5(-1) = 1 + (-1)^3 =', 1 + (-1) ** 3)
H11 = [[M[i + j + 3] for j in range(11)] for i in range(11)]
print('det H11(-1) =', det_frac(H11), ' t_11(-1) =', sum((-1) ** (3 * k) for k in range(4)))
M1 = motzkin_at(1, 12)
print('check M_k(1):', M1[:10])
