"""371607 exact certificate for a binary automaton (Venturi, Semigroup Forum 2026, Conjecture 5.2).
Q = {0,..,n-1}; letters given as image lists. Right action q.u. Checks exactly (Fractions):
 (1) closure of reachable image sets Q.u: sizes, synchronizing, no size 2; shortest reset length;
 (2) synchronized representation on W = {v in Q^Q : sum v = 0}, basis v_i = q_i - q_0 (i=1..n-1):
     choose (n-1)^2 words whose matrices are linearly independent over Q (exact determinant != 0),
     then express every elementary matrix E_ij as an explicit Q-combination (certificate).
usage: automata_certificate.py OUT.json a0,a1,... b0,b1,... [more letters]
"""
import sys, json, itertools
from fractions import Fraction
from collections import deque
out = sys.argv[1]
letters = {chr(97 + i): tuple(int(x) for x in s.split(',')) for i, s in enumerate(sys.argv[2:])}
n = len(next(iter(letters.values())))
m = n - 1

# (1) reachable image sets with BFS (shortest words)
full = frozenset(range(n)); dist = {full: ''}; dq = deque([full])
while dq:
    S = dq.popleft()
    for c, f in sorted(letters.items()):
        T = frozenset(f[x] for x in S)
        if T not in dist:
            dist[T] = dist[S] + c; dq.append(T)
sizes = sorted({len(S) for S in dist})
singles = [w for S, w in dist.items() if len(S) == 1]
reset = min(singles, key=len) if singles else None
print('reachable image sets', len(dist), 'sizes', sizes, 'shortest reset word', reset, len(reset) if reset else None)
assert 2 not in sizes and 1 in sizes

# (2) word matrices: row i (basis v_{i+1}) -> coordinates of v_{i+1}.u in basis v_1..v_m
def apply(word, q):
    for c in word:
        q = letters[c][q]
    return q
def mat(word):
    M = [[0] * m for _ in range(m)]
    q0 = apply(word, 0)
    for i in range(1, n):
        for s, sg in ((apply(word, i), 1), (q0, -1)):
            if s != 0:
                M[i - 1][s - 1] += sg
    return M

# enumerate distinct transformations by BFS on words (shortlex), keep independent matrices
idw = ''; seen = {tuple(range(n)): ''}; dq = deque([''])
basis_words = []; rows = []  # rows: flattened, reduced echelon over Q for independence test
ech = {}
def reduce(v):
    v = list(v)
    for c, r in ech.items():
        if v[c] != 0:
            t = v[c]; v = [x - t * y for x, y in zip(v, r)]
    return v
while dq and len(basis_words) < m * m:
    w = dq.popleft()
    v = [Fraction(x) for x in sum(mat(w), [])]
    rv = reduce(v)
    nz = next((i for i, x in enumerate(rv) if x != 0), None)
    if nz is not None:
        ech[nz] = [x / rv[nz] for x in rv]; basis_words.append(w)
    for c in sorted(letters):
        w2 = w + c
        t = tuple(apply(w2, q) for q in range(n))
        if t not in seen:
            seen[t] = w2; dq.append(w2)
print('independent word matrices found', len(basis_words), 'of', m * m)
assert len(basis_words) == m * m
# solve E_ij = sum_k c_k M_k exactly (Gauss-Jordan on the m^2 x m^2 system)
A = [[Fraction(x) for x in sum(mat(w), [])] for w in basis_words]  # rows = words
# we need coefficients c with c^T A = e_t for each target t: solve A^T c = e_t
At = [[A[k][t] for k in range(m * m)] for t in range(m * m)]
N = m * m
aug = [At[t] + [Fraction(int(t == s)) for s in range(N)] for t in range(N)]
for col in range(N):
    piv = next(r for r in range(col, N) if aug[r][col] != 0)
    aug[col], aug[piv] = aug[piv], aug[col]
    p = aug[col][col]; aug[col] = [x / p for x in aug[col]]
    for r in range(N):
        if r != col and aug[r][col] != 0:
            t = aug[r][col]; aug[r] = [x - t * y for x, y in zip(aug[r], aug[col])]
inv = [row[N:] for row in aug]  # inverse of At
coeffs = {}
for t in range(N):
    c = [inv[k][t] for k in range(N)]  # column t of inverse
    # verify exactly
    comb = [sum(c[k] * A[k][s] for k in range(N)) for s in range(N)]
    assert comb == [Fraction(int(s == t)) for s in range(N)]
    coeffs['E_%d_%d' % (t // m, t % m)] = [str(x) for x in c]
cert = {'n': n, 'letters': {k: list(v) for k, v in letters.items()},
        'reachable_image_sets': sorted([sorted(S) for S in dist], key=lambda s: (len(s), s)),
        'image_sizes': sizes, 'shortest_reset_word': reset,
        'basis_words': basis_words, 'basis_matrices': [mat(w) for w in basis_words],
        'elementary_matrix_coefficients': coeffs,
        'convention': 'row i-1 of mat(w) = coordinates of (q_i - q_0).w in basis (q_j - q_0), j=1..n-1; right action'}
open(out, 'x').write(json.dumps(cert, indent=1) + '\n')
print('certificate written', out, 'words', basis_words)
