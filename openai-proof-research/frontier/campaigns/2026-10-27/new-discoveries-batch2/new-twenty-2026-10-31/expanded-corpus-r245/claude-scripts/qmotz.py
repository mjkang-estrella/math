"""Oh-Scrimshaw arXiv:1805.00113 Conjecture A.3 (MathDB 339077), intended reading:
det[M_{i+j+3}]_{i,j<n} = (-1)^{floor(n/3)} q^{c_n} g_n(q), g_n in Z>=0[q], g_n(0) != 0;
n = 1 mod 3: g_n = (q+1)^2 t_n^2; n = 2 mod 3: t_n | g_n; t_n = sum_{k<=floor(n/3)} q^{3k}.
Polynomials: lists of ints (index = degree).  Determinants by fraction-free Bareiss over Z[q].
usage: qmotz.py SHIFT NMAX_DIRECT NMAX TAG
Direct Hankel determinants for n <= NMAX_DIRECT; for larger n use the block identity
det H^(r)_n = q^{n(n-1)(n-2)/3 + n(n-1)/2} det (B^r)_[0,n), B = K D (K tridiagonal ones,
D = diag(q^h)), cross-checked against the direct values where both are computed."""
import json
import os
import sys
import time

LANE = '/home/mj-kang/Documents/Dev/math/openai-proof-research/frontier/campaigns/2026-10-27/new-discoveries-batch2/new-twenty-2026-10-31/expanded-corpus-r245'
OUT = os.path.join(LANE, 'outputs', 'claude-qmotz')


def trim(p):
    while p and p[-1] == 0:
        p.pop()
    return p


def add(a, b):
    r = [0] * max(len(a), len(b))
    for i, x in enumerate(a):
        r[i] += x
    for i, x in enumerate(b):
        r[i] += x
    return trim(r)


def sub(a, b):
    return add(a, [-x for x in b])


def mul(a, b):
    if not a or not b:
        return []
    r = [0] * (len(a) + len(b) - 1)
    for i, x in enumerate(a):
        if x:
            for j, y in enumerate(b):
                r[i + j] += x * y
    return trim(r)


def divexact(a, b):
    a = list(a)
    b = trim(list(b))
    if not a:
        return []
    q = [0] * (len(a) - len(b) + 1)
    lb = b[-1]
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1]
        if c % lb:
            raise ArithmeticError('not exact')
        c //= lb
        q[i] = c
        if c:
            for j, y in enumerate(b):
                a[i + j] -= c * y
    if any(a):
        raise ArithmeticError('remainder')
    return trim(q)


def divmod_poly(a, b):
    a = list(a)
    b = trim(list(b))
    if len(a) < len(b):
        return [], trim(a)
    q = [0] * (len(a) - len(b) + 1)
    lb = b[-1]
    for i in range(len(a) - len(b), -1, -1):
        c = a[i + len(b) - 1]
        if c % lb:
            return None, None
        c //= lb
        q[i] = c
        if c:
            for j, y in enumerate(b):
                a[i + j] -= c * y
    return trim(q), trim(a)


def bareiss(M):
    n = len(M)
    A = [[list(x) for x in row] for row in M]
    sign = 1
    prev = [1]
    for k in range(n - 1):
        if not A[k][k]:
            sw = next((i for i in range(k + 1, n) if A[i][k]), None)
            if sw is None:
                return []
            A[k], A[sw] = A[sw], A[k]
            sign = -sign
        for i in range(k + 1, n):
            for j in range(k + 1, n):
                A[i][j] = divexact(sub(mul(A[i][j], A[k][k]), mul(A[i][k], A[k][j])), prev)
        prev = A[k][k]
    d = A[n - 1][n - 1]
    return [sign * x for x in d]


def motzkin(N):
    M = [[1]]
    for n in range(N):
        s = list(M[n])
        for r in range(n):
            s = add(s, mul([0] * (r + 1) + [1], mul(M[r], M[n - r - 1])))
        M.append(s)
    return M


def block_det(n, r):
    m = n + r + 2
    B = [[([0] * j + [1]) if abs(h - j) <= 1 else [] for j in range(m)] for h in range(m)]
    P = [[([1] if h == j else []) for j in range(m)] for h in range(m)]
    for _ in range(r):
        P = [[trim(sum_list([mul(P[h][k], B[k][j]) for k in range(m)])) for j in range(m)] for h in range(m)]
    sub_ = [row[:n] for row in P[:n]]
    d = bareiss(sub_)
    beta = n * (n - 1) * (n - 2) // 3 + n * (n - 1) // 2
    return trim([0] * beta + d) if d else []


def sum_list(ps):
    r = []
    for p in ps:
        r = add(r, p)
    return r


def main():
    os.makedirs(OUT, exist_ok=True)
    shift, ndir, nmax, tag = int(sys.argv[1]), int(sys.argv[2]), int(sys.argv[3]), sys.argv[4]
    t0 = time.time()
    M = motzkin(2 * ndir + shift + 2)
    rows = []
    for n in range(1, nmax + 1):
        rec = {'n': n}
        dblk = block_det(n, shift)
        rec['block'] = dblk
        if n <= ndir:
            H = [[M[i + j + shift] for j in range(n)] for i in range(n)]
            ddir = bareiss(H)
            rec['direct_matches_block'] = (ddir == dblk)
        d = dblk
        c = next(i for i, x in enumerate(d) if x)
        g = d[c:]
        sgn = 1 if g[-1] > 0 else -1
        expected_sign = (-1) ** (n // 3)
        gs = [sgn * x for x in g]
        rec['c_n'] = c
        rec['sign_ok'] = (sgn == expected_sign)
        rec['g_nonneg'] = all(x >= 0 for x in gs)
        rec['g_negative_coeffs'] = [(i, x) for i, x in enumerate(gs) if x < 0][:10]
        tn = [0] * (3 * (n // 3) + 1)
        for k in range(n // 3 + 1):
            tn[3 * k] = 1
        if n % 3 == 1:
            target = mul(mul([1, 1], [1, 1]), mul(tn, tn))
            rec['n1_formula_ok'] = (gs == target)
        if n % 3 == 2:
            q_, r_ = divmod_poly(gs, tn)
            rec['n2_divisible'] = (r_ == [])
        if shift == 3 and n % 3 == 0:
            rec['g_n'] = gs
        rec['deg'] = len(d) - 1
        rows.append({k: v for k, v in rec.items() if k != 'block'})
        print(json.dumps({k: v for k, v in rec.items() if k not in ('block', 'g_n')}), flush=True)
        if time.time() - t0 > 85:
            break
    with open(os.path.join(OUT, f'qmotz-{tag}.json'), 'x') as f:
        json.dump(rows, f, indent=1)


if __name__ == '__main__':
    main()
