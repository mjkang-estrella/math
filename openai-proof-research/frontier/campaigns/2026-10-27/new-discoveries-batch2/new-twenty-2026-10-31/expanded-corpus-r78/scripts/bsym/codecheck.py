# Independent diagnostic: enumerate ker H over F_p for the recursive construction and compute min b-weight.
import sys, json, itertools, os
sys.path.insert(0, os.path.dirname(__file__))
from recursive import S
def kernel_basis(H, n, p):
    # H: list of b rows (lists length n) over F_p; return basis of nullspace
    A = [row[:] for row in H]; b = len(A); piv = []; rk = 0
    for c in range(n):
        r = next((i for i in range(rk, b) if A[i][c] % p), None)
        if r is None: continue
        A[rk], A[r] = A[r], A[rk]; iv = pow(A[rk][c], -1, p); A[rk] = [x * iv % p for x in A[rk]]
        for i in range(b):
            if i != rk and A[i][c] % p:
                f = A[i][c]; A[i] = [(x - f*y) % p for x, y in zip(A[i], A[rk])]
        piv.append(c); rk += 1
    free = [c for c in range(n) if c not in piv]; basis = []
    for f in free:
        v = [0]*n; v[f] = 1
        for i, c in enumerate(piv): v[c] = (-A[i][f]) % p
        basis.append(v)
    return basis, rk
def wtb(x, b):
    n = len(x); return sum(1 for i in range(n) if any(x[(i + j) % n] for j in range(b)))
res = []
for p in (2, 3, 5):
    for b in range(2, 6):
        for n in range(2*b, 3*b + 3):
            if p ** (n - b) > 300000: continue
            seq = S(b, n); H = [[seq[j][k] % p for j in range(n)] for k in range(b)]
            B, rk = kernel_basis(H, n, p)
            mn = None; size = 0
            for coeffs in itertools.product(range(p), repeat=len(B)):
                size += 1
                if not any(coeffs): continue
                x = [sum(c * v[i] for c, v in zip(coeffs, B)) % p for i in range(n)]
                w = wtb(x, b); mn = w if mn is None else min(mn, w)
            res.append({'q': p, 'b': b, 'n': n, 'rank': rk, 'size': size, 'expected_size': p ** (n - b), 'min_b_weight': mn, 'ok': rk == b and size == p ** (n - b) and mn == 2*b})
bad = [r for r in res if not r['ok']]
print(json.dumps({'cases': len(res), 'bad': bad, 'sample': res[:3]}))
