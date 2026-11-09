"""Cross-checks: first q-Motzkin numbers; shift-2 n=3 determinant (Omega certificate says q^11(1+q^2+q^3));
shift-3 n=5 determinant computed directly by Bareiss and by cofactor expansion (independent)."""
import importlib.util
import itertools
import sys

spec = importlib.util.spec_from_file_location('qm', sys.argv[1])
Q = importlib.util.module_from_spec(spec)
spec.loader.exec_module(Q)
M = Q.motzkin(16)
for k in range(7):
    print('M', k, M[k], 'M(1)=', sum(M[k]))
H2 = [[M[i + j + 2] for j in range(3)] for i in range(3)]
print('shift2 n3 direct', Q.bareiss(H2), 'block', Q.block_det(3, 2))


def leibniz(A):
    n = len(A)
    tot = []
    for perm in itertools.permutations(range(n)):
        inv = sum(1 for i in range(n) for j in range(i + 1, n) if perm[i] > perm[j])
        p = [1]
        for i in range(n):
            p = Q.mul(p, A[i][perm[i]])
        tot = Q.add(tot, p if inv % 2 == 0 else [-x for x in p])
    return tot


H3 = [[M[i + j + 3] for j in range(5)] for i in range(5)]
d1 = Q.bareiss(H3)
d2 = leibniz(H3)
print('shift3 n5 bareiss==leibniz', d1 == d2)
c = next(i for i, x in enumerate(d2) if x)
print('shift3 n5 det = sign', 1 if d2[-1] > 0 else -1, 'q^', c, 'times', d2[c:])
g = [abs(x) for x in d2[c:]]
qq, r = Q.divmod_poly(g, [1, 0, 0, 1])
print('g5 mod (1+q^3) remainder', r)
# value at q = -1: t_5(-1) = 0, so t_5 | g_5 would force g_5(-1) = 0
print('g5(-1) =', sum(x * (-1) ** i for i, x in enumerate(g)))
