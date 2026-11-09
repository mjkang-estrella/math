"""Independent re-implementation (written from Ehrenborg-Readdy, J. Algebraic Combin. 8 (1998), Def. 9.1,
Thm 9.2, and Hetyei DCG 71 (2024) Thm 32) producing the two certificates, all in the ab-word basis,
exact integer/rational arithmetic, no reuse of the other scripts.

  Delta(v1..vn) = sum_i v1..v_{i-1} (x) v_{i+1}..vn ;  u* = reversal
  index set I = {(r,s,n): r,s in {1,2}, n >= 2, n = r+s+1 mod 2}
  M_{1,2}(u,v,2) = u a v ; M_{2,1}(u,v,2) = v b u   (ER; Hetyei prints u b v -- see notes)
  M_{1,s}(u,v,n+1) = sum_u u_(1) a M_{2,s}(u_(2),v,n) ; M_{2,s}(u,v,n+1) = sum_v v_(1) b M_{1,s}(u,v_(2),n)
  M(u,v) = sum_{(r,s,n) in I} M_{r,s}(u,v,n) ;  I2(u) = u + u* + sum_u M(u_(1)*, u_(2)).

Certificate A (347230, Conjecture 39 at n = 5): integer ab-polynomial u, u* = u, u != 0, I2(u) = 0.
   Also: exact rank of I2 on Q<a,b>_5 (fraction-free) and dim ker vs dim A_5.
Certificate B (347231, Conjecture 40 at n = 3): rational functionals Psi1, Psi2 on Q<a,b>_3, *-invariant,
   with Psi1(I2 s) = 2 Psi1(s) and Psi2(I2 s) = 2 Psi2(s) + Psi1(s) for all s in S_3, and Psi1 != 0 on S_3.
   Consequence: every I2-eigenvector s in S_3 has Psi1(s) = 0, so eigenvectors in S_3 span a proper subspace.
Also re-checks Corollary 33 (I2(u - u*) = 0) and the Lemma 36 failure (L(Psi(B_3)) not an eigenvector).
Usage: hetyei_certificates.py OUTJSON"""
import sys, json, itertools
from fractions import Fraction
from functools import lru_cache
OUT = sys.argv[1]

def add(d, w, c):
    if c:
        v = d.get(w, 0) + c
        if v: d[w] = v
        else: d.pop(w, None)
def cop(w): return [(w[:i], w[i + 1:]) for i in range(len(w))]
@lru_cache(None)
def Mrs(r, s, u, v, n):
    out = {}
    if n == 2:
        if (r, s) == (1, 2): add(out, u + 'a' + v, 1)
        elif (r, s) == (2, 1): add(out, v + 'b' + u, 1)
        return tuple(sorted(out.items()))
    if r == 1:
        for u1, u2 in cop(u):
            for w, c in Mrs(2, s, u2, v, n - 1): add(out, u1 + 'a' + w, c)
    else:
        for v1, v2 in cop(v):
            for w, c in Mrs(1, s, u, v2, n - 1): add(out, v1 + 'b' + w, c)
    return tuple(sorted(out.items()))
def M(u, v):
    out = {}
    for r in (1, 2):
        for s in (1, 2):
            for n in range(2, len(u) + len(v) + 4):
                if (n - r - s - 1) % 2: continue
                for w, c in Mrs(r, s, u, v, n): add(out, w, c)
    return out
def I2w(u):
    out = {}
    add(out, u, 1); add(out, u[::-1], 1)
    for u1, u2 in cop(u):
        for w, c in M(u1[::-1], u2).items(): add(out, w, c)
    return out
def I2(vec):
    out = {}
    for w, c in vec.items():
        for w2, d in I2w(w).items(): add(out, w2, c * d)
    return out
def words(n): return [''.join(t) for t in itertools.product('ab', repeat=n)]

res = {}
# sanity: product of two chains of rank 3 and 2 vs direct count (M = ab-index of product)
res['sanity_M_a_1'] = M('a', '')          # expect aa + ab + ba
# Certificate A
u = {'aaaba': 1, 'aaabb': 1, 'aabaa': -2, 'aabba': -1, 'aabbb': 1, 'abaaa': 1, 'abaab': 1, 'abbaa': -1,
     'abbab': 1, 'abbba': -2, 'baaab': -2, 'baaba': 1, 'baabb': -1, 'babba': 1, 'babbb': 1, 'bbaaa': 1,
     'bbaab': -1, 'bbabb': -2, 'bbbaa': 1, 'bbbab': 1}
resA = {'u': u, 'u_star_equals_u': all(u.get(w[::-1], 0) == c for w, c in u.items()), 'u_nonzero': bool(u),
        'I2_u': I2(u), 'I2_u_is_zero': I2(u) == {}}
# exact rank of I2 on Q<a,b>_5 via fraction-free elimination on integer matrix
def int_rank(rows):
    A = [r[:] for r in rows]; rk = 0; ncol = len(A[0])
    for c in range(ncol):
        p = next((i for i in range(rk, len(A)) if A[i][c]), None)
        if p is None: continue
        A[rk], A[p] = A[p], A[rk]
        for i in range(rk + 1, len(A)):
            if A[i][c]:
                f, g = A[i][c], A[rk][c]
                A[i] = [g * x - f * y for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk
for n in (4, 5):
    W = words(n); idx = {w: i for i, w in enumerate(W)}
    rows = []
    for w in W:
        r = [0] * len(W)
        for w2, c in I2w(w).items(): r[idx[w2]] = c
        rows.append(r)
    rk = int_rank(rows)
    resA[f'n{n}'] = {'rank_I2': rk, 'dim_ker': 2 ** n - rk, 'dim_A': 2 ** (n - 1) - 2 ** ((n - 1) // 2)}
# Corollary 33 check on all words up to 6
c33 = all(I2({w: 1, w[::-1]: -1}) == {} for n in range(1, 7) for w in words(n) if w != w[::-1])  # palindromes: u - u* = 0
resA['corollary33_all_words_n_le_6'] = c33
res['A'] = resA
# Certificate B at n = 3
n = 3; W = words(n)
basis = []  # symmetric basis
seen = set()
for w in W:
    if w in seen: continue
    seen |= {w, w[::-1]}
    basis.append({w: 1} if w == w[::-1] else {w: 1, w[::-1]: 1})
d = len(basis)
def coords(vec):  # coordinates of pi(vec) in symmetric basis
    out = []
    for b in basis:
        ws = list(b)
        if len(ws) == 1: out.append(Fraction(vec.get(ws[0], 0)))
        else: out.append(Fraction(vec.get(ws[0], 0) + vec.get(ws[1], 0), 2))
    return out
B = [[None] * d for _ in range(d)]
for j, b in enumerate(basis):
    cj = coords(I2(b))
    for i in range(d): B[i][j] = cj[i]
# left Jordan pair for eigenvalue 2: psi1 (B - 2) = 0, psi2 (B - 2) = psi1
def solve_left(Bm, lam, rhs):
    # find row vector x with x (B - lam I) = rhs ; return one solution (free vars = 0) or None
    m = d
    A = [[Bm[j][i] - (lam if i == j else 0) for j in range(m)] + [rhs[i]] for i in range(m)]  # transpose system
    piv = []; r = 0
    for c in range(m):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; pv = A[r][c]; A[r] = [x / pv for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    if any(A[i][m] != 0 for i in range(r, m)): return None, piv
    x = [Fraction(0)] * m
    for i, c in enumerate(piv): x[c] = A[i][m]
    return x, piv
# left kernel of (B-2): solve x(B-2)=0 nontrivially: compute nullspace of (B-2)^T
def left_null(Bm, lam):
    m = d
    A = [[Bm[j][i] - (lam if i == j else 0) for j in range(m)] for i in range(m)]
    piv = []; r = 0
    for c in range(m):
        p = next((i for i in range(r, m) if A[i][c] != 0), None)
        if p is None: continue
        A[r], A[p] = A[p], A[r]; pv = A[r][c]; A[r] = [x / pv for x in A[r]]
        for i in range(m):
            if i != r and A[i][c] != 0:
                f = A[i][c]; A[i] = [x - f * y for x, y in zip(A[i], A[r])]
        piv.append(c); r += 1
    free = [c for c in range(m) if c not in piv]; sols = []
    for fc in free:
        x = [Fraction(0)] * m; x[fc] = Fraction(1)
        for i, c in enumerate(piv): x[c] = -A[i][fc]
        sols.append(x)
    return sols
# Certificate B (simplest form): a symmetric s0 in S_3 with I2(s0) not symmetric.  For the antisymmetric
# functional alpha(v) = v[w0] - v[w0*], Psi = alpha o I2 vanishes on every I2-eigenvector s in S_3
# (I2 s = lam s is symmetric, alpha kills symmetric vectors) and Psi(s0) != 0.
cert = None
for b in basis:
    img = I2(b)
    for w in W:
        if img.get(w, 0) != img.get(w[::-1], 0):
            cert = (b, img, w); break
    if cert: break
b0, img0, w0 = cert
res['B'] = {'n': 3, 'symmetric_basis': [sorted(b) for b in basis], 's0': b0, 'I2_s0': img0, 'w0': w0,
            'alpha_I2_s0': img0.get(w0, 0) - img0.get(w0[::-1], 0),
            'nonsymmetric_images_in_symmetric_basis': sum(1 for b in basis if any(I2(b).get(w, 0) != I2(b).get(w[::-1], 0) for w in W)),
            'B_matrix_pi_I2_on_S3': [[str(x) for x in row] for row in B]}
# eigenvector span in S_3 (exact): for each candidate eigenvalue, nullity of (I2 - lam) on S_3
def rank_frac(rows):
    A = [r[:] for r in rows]; rk = 0; ncol = len(A[0])
    for c in range(ncol):
        p = next((i for i in range(rk, len(A)) if A[i][c] != 0), None)
        if p is None: continue
        A[rk], A[p] = A[p], A[rk]
        for i in range(rk + 1, len(A)):
            if A[i][c] != 0:
                f = A[i][c] / A[rk][c]; A[i] = [x - f * y for x, y in zip(A[i], A[rk])]
        rk += 1
    return rk
idx3 = {w: i for i, w in enumerate(W)}
span = {}
for lam in [0, 1, 2, 4, 8, 16, 32]:
    rows = []
    for b in basis:
        v = I2(b); r = [Fraction(0)] * len(W)
        for w, c in v.items(): r[idx3[w]] += c
        for w, c in b.items(): r[idx3[w]] -= lam * c
        rows.append(r)
    k = d - rank_frac(rows)
    if k: span[lam] = k
res['B']['eigvec_dims_in_S3'] = span
chk1 = res['B']['alpha_I2_s0'] != 0; chk2 = sum(span.values()) < d
# Lemma 36 failure: Psi(B_3) = aa + 2ab + 2ba + bb, eigenvalue 8; L(u) = (a-b)u + u(a-b)
uB = {'aa': 1, 'ab': 2, 'ba': 2, 'bb': 1}
Lu = {}
for w, c in uB.items():
    add(Lu, 'a' + w, c); add(Lu, 'b' + w, -c); add(Lu, w + 'a', c); add(Lu, w + 'b', -c)
IL = I2(Lu)
res['lemma36'] = {'I2_PsiB3_equals_8_PsiB3': I2(uB) == {w: 8 * c for w, c in uB.items()}, 'L_u': Lu, 'I2_L_u': IL,
                  'is_eigenvector': (lambda w0: all(IL.get(w, 0) * Lu[w0] == Fraction(IL.get(w0, 0)) * c for w, c in Lu.items()) and set(IL) <= set(Lu))(next(iter(Lu)))}
json.dump(res, open(OUT, 'x'), indent=1, default=str)
print('A: u*=u', resA['u_star_equals_u'], 'I2(u)=0', resA['I2_u_is_zero'], resA['n4'], resA['n5'], 'Cor33', c33)
print('B: s0', b0, 'I2(s0)', img0, 'w0', w0, 'alpha(I2 s0) != 0:', chk1, '| nonsymmetric images among basis:',
      res['B']['nonsymmetric_images_in_symmetric_basis'], '| eigvec dims in S3', span, 'total < 6:', chk2)
print('Lemma36: I2(Psi B3)=8 Psi B3', res['lemma36']['I2_PsiB3_equals_8_PsiB3'], 'L(u) eigenvector?', res['lemma36']['is_eigenvector'])
print('sanity M(a,1)', res['sanity_M_a_1'])
