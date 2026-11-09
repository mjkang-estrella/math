"""Exhaustive test of the Ellison-Jouve-Stone conjecture (arXiv:2212.07706, MathDB 381851).

For every p x q binary matrix class M(R,C) (R in a chunk of row-sum vectors), compute the
oriented switching graph G(R,C) (arc A -> A + C_{i,j,k,l} when A has a negative checkerboard
on rows i<j, columns k<l), its reachability closure, and for every ordered pair (A, A') in the
class:
  cond_i  : M = A' - A is a nonnegative integer combination of unitary switching matrices
            (equivalently, T = 2D prefix sums of M over [1..i]x[1..k], i<p, k<q, are >= 0);
  cond_ii : for every level i >= 1 each 4-connected component of P_i = {cells: t >= i} is
            simply connected (its complement in the frame-extended grid is 4-connected);
  reach   : A ->* A'.
Reports (a) pairs with cond_i & cond_ii & not reach  ("if"-direction counterexamples),
        (b) per (R,C,M): cond_i & not cond_ii & every pair with difference M reachable
            (fixed-(R,C) "only if" failures, recorded separately), and counts.
usage: checker.py p q chunk_index n_chunks
"""
import sys, json
from itertools import combinations, product

p, q, ci, nc = map(int, sys.argv[1:5])

def rows_with_sum(s):
    return [sum(1 << c for c in cs) for cs in combinations(range(q), s)]

Rvecs = list(product(range(q + 1), repeat=p))
Rvecs = [R for idx, R in enumerate(Rvecs) if idx % nc == ci]

def bit(r, c):
    return (r >> c) & 1

def prefix(A):
    # T[i][k] for i in 0..p-2, k in 0..q-2 : sum of A over rows<=i, cols<=k
    T = []
    for i in range(p - 1):
        row = []
        for k in range(q - 1):
            row.append(sum(bit(A[a], b) for a in range(i + 1) for b in range(k + 1)))
        T.append(row)
    return T

FIELD = 7
def pack(T):
    v = 0
    for row in T:
        for x in row:
            v = (v << FIELD) | x
    return v
NF = (p - 1) * (q - 1)
GUARD = sum(1 << (FIELD * f + FIELD - 1) for f in range(NF))

def simply_connected_levels(Tm):
    mx = max((x for row in Tm for x in row), default=0)
    P, Q = p - 1, q - 1
    for lev in range(1, mx + 1):
        inside = [[Tm[i][k] >= lev for k in range(Q)] for i in range(P)]
        # complement in frame-extended grid (P+2)x(Q+2) must be 4-connected
        seen = set(); stack = [(-1, -1)]; seen.add((-1, -1))
        while stack:
            i, k = stack.pop()
            for di, dk in ((1, 0), (-1, 0), (0, 1), (0, -1)):
                a, b = i + di, k + dk
                if -1 <= a <= P and -1 <= b <= Q and (a, b) not in seen:
                    if 0 <= a < P and 0 <= b < Q and inside[a][b]:
                        continue
                    seen.add((a, b)); stack.append((a, b))
        total_out = (P + 2) * (Q + 2) - sum(map(sum, inside))
        if len(seen) != total_out:
            return False
    return True

stats = dict(p=p, q=q, chunk=ci, nchunks=nc, classes=0, matrices=0, pairs_cond_i=0,
             pairs_cond_i_unreach=0, if_counterexamples=0, onlyif_fixedRC_failures=0, max_class=0)
ifce = []; onlyif = []
for R in Rvecs:
    choices = [rows_with_sum(s) for s in R]
    classes = {}
    for A in product(*choices):
        C = tuple(sum(bit(A[r], c) for r in range(p)) for c in range(q))
        classes.setdefault(C, []).append(A)
    for C, mats in classes.items():
        s = len(mats); stats['classes'] += 1; stats['matrices'] += s
        stats['max_class'] = max(stats['max_class'], s)
        if s < 2:
            continue
        index = {A: n for n, A in enumerate(mats)}
        I = [sum((r + 1) * (c + 1) * bit(A[r], c) for r in range(p) for c in range(q)) for A in mats]
        succ = []
        for A in mats:
            out = []
            for i, j in combinations(range(p), 2):
                X = A[j] & ~A[i]; Y = A[i] & ~A[j]   # k: A[i][k]=0,A[j][k]=1 ; l: A[i][l]=1,A[j][l]=0
                if not X or not Y:
                    continue
                for k in range(q):
                    if not (X >> k) & 1: continue
                    for l in range(k + 1, q):
                        if (Y >> l) & 1:
                            B = list(A)
                            B[i] ^= (1 << k) | (1 << l); B[j] ^= (1 << k) | (1 << l)
                            out.append(index[tuple(B)])
            succ.append(out)
        order = sorted(range(s), key=lambda n: -I[n])
        reach = [0] * s
        for n in order:
            r = 1 << n
            for m in succ[n]:
                r |= reach[m]
            reach[n] = r
        Ts = [prefix(A) for A in mats]
        pk = [pack(T) for T in Ts]
        byM = {}
        for a in range(s):
            pa = pk[a]; ra = reach[a]
            for b in range(s):
                if a == b: continue
                if ((pk[b] | GUARD) - pa) & GUARD != GUARD:
                    continue
                stats['pairs_cond_i'] += 1
                ok = (ra >> b) & 1
                M = tuple(tuple(bit(mats[b][r], c) - bit(mats[a][r], c) for c in range(q)) for r in range(p))
                e = byM.setdefault(M, [True, a, b])
                if not ok:
                    e[0] = False
                    stats['pairs_cond_i_unreach'] += 1
                    Tm = [[Ts[b][i][k] - Ts[a][i][k] for k in range(q - 1)] for i in range(p - 1)]
                    if simply_connected_levels(Tm):
                        stats['if_counterexamples'] += 1
                        if len(ifce) < 20:
                            ifce.append(dict(R=R, C=C, A=[[bit(mats[a][r], c) for c in range(q)] for r in range(p)],
                                             A2=[[bit(mats[b][r], c) for c in range(q)] for r in range(p)], T=Tm))
        for M, (allok, a, b) in byM.items():
            if allok:
                Tm = [[Ts[b][i][k] - Ts[a][i][k] for k in range(q - 1)] for i in range(p - 1)]
                if not simply_connected_levels(Tm):
                    stats['onlyif_fixedRC_failures'] += 1
                    if len(onlyif) < 5:
                        onlyif.append(dict(R=R, C=C, M=M, T=Tm))
print(json.dumps(dict(stats=stats, if_counterexamples=ifce, onlyif_fixedRC_examples=onlyif)))
