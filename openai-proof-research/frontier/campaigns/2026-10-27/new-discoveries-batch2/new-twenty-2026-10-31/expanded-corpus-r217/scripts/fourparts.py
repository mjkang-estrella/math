# Conjecture 4 of Bogdanov-Petrov-Sadovnichiy-Ushakov (arXiv:2603.18253v1), MathDB 373706.
# Data: A = [u1,v1] (n1 x k1, row sums k2, col sums n2), B = [u2,v2] (n2 x k2, row sums k1, col sums n1).
# A bijection psi exists iff there are alpha: R1 x L2 -> L1 and delta: R1 x L2 -> R2 with
#   #{c : alpha(b,c)=a} = A[a][b]  for all a,b;   #{b : delta(b,c)=d} = B[c][d] for all c,d;
#   (b,c) -> (alpha,delta) a bijection onto L1 x R2.
# (Proof: given psi, for e in E1 put b=v1(e), c=u2(psi e); W condition => (b,c) determines e uniquely;
#  set alpha=u1(e), delta=v2(psi e). Conversely build psi from the quadruples.)
# Feasibility depends only on the S_n1 x S_k1 orbit of A and the S_n2 x S_k2 orbit of B.
# usage: fourparts.py n1 k1 n2 k2 [maxpairs]
import sys, itertools

def matrices(rows, cols, rs, cs):
    # all rows x cols nonneg int matrices with row sums rs, col sums cs
    res = []
    def rec(i, rem, acc):
        if i == rows:
            if all(x == 0 for x in rem): res.append(tuple(acc))
            return
        def rowrec(j, left, row):
            if j == cols:
                if left == 0: rec(i + 1, [rem[t] - row[t] for t in range(cols)], acc + [tuple(row)])
                return
            for x in range(min(left, rem[j]) + 1):
                rowrec(j + 1, left - x, row + [x])
        rowrec(0, rs, [])
    rec(0, [cs] * cols, [])
    return res

def canon(M):
    rows = len(M)
    best = None
    for perm in itertools.permutations(range(rows)):
        cols = sorted(tuple(M[perm[i]][j] for i in range(rows)) for j in range(len(M[0])))
        key = tuple(cols)
        if best is None or key < best: best = key
    return best

def classes(rows, cols, rs, cs):
    # orderly: matrix = multiset of `cols` column vectors (length rows, sum cs), row sums rs
    colvecs = []
    def cv(i, left, acc):
        if i == rows - 1:
            colvecs.append(tuple(acc + [left])); return
        for x in range(left, -1, -1): cv(i + 1, left - x, acc + [x])
    cv(0, cs, [])
    colvecs = [c for c in colvecs if max(c) <= rs]
    seen = {}
    def rec(start, k, rem, chosen):
        if k == 0:
            if all(r == 0 for r in rem):
                M = tuple(tuple(chosen[j][i] for j in range(cols)) for i in range(rows))
                c = canon(M)
                if c not in seen: seen[c] = M
            return
        for t in range(start, len(colvecs)):
            v = colvecs[t]
            if all(v[i] <= rem[i] for i in range(rows)):
                # remaining capacity check: need sum(rem) == k*cs automatically
                rec(t, k - 1, [rem[i] - v[i] for i in range(rows)], chosen + [v])
    rec(0, cols, [rs] * rows, [])
    return list(seen.values())

def solve(A, B, n1, k1, n2, k2):
    # A[a][b], B[c][d]; cells (b,c); assign (a,d)
    rowcnt = [[A[a][b] for a in range(n1)] for b in range(k1)]
    colcnt = [[B[c][d] for d in range(k2)] for c in range(n2)]
    used = [[False] * k2 for _ in range(n1)]
    cells = [(b, c) for b in range(k1) for c in range(n2)]
    sol = {}
    def rec(i):
        if i == len(cells): return True
        b, c = cells[i]
        rc = rowcnt[b]; cc = colcnt[c]
        for a in range(n1):
            if rc[a] == 0: continue
            ua = used[a]
            for d in range(k2):
                if cc[d] == 0 or ua[d]: continue
                rc[a] -= 1; cc[d] -= 1; ua[d] = True
                sol[(b, c)] = (a, d)
                if rec(i + 1): return True
                rc[a] += 1; cc[d] += 1; ua[d] = False
        return False
    return dict(sol) if rec(0) else None

class Undecided(Exception): pass

def solve_mrv(A, B, n1, k1, n2, k2, limit=200000):
    # exact cover: cells (b,c) <-> pairs (a,d), option valid iff rowcnt[b][a]>0 and colcnt[c][d]>0.
    rowcnt = [[A[a][b] for a in range(n1)] for b in range(k1)]
    colcnt = [[B[c][d] for d in range(k2)] for c in range(n2)]
    freecells = set((b, c) for b in range(k1) for c in range(n2))
    freepairs = set((a, d) for a in range(n1) for d in range(k2))
    sol = {}; nodes = [0]
    def rec():
        nodes[0] += 1
        if nodes[0] > limit: raise Undecided
        if not freecells: return True
        # candidate options per cell and per pair
        best = None
        fa = {}; fd = {}
        for (a, d) in freepairs:
            fa.setdefault(a, []).append(d)
        pc = {}
        for (b, c) in freecells:
            rc = rowcnt[b]; cc = colcnt[c]
            opts = [(a, d) for a in range(n1) if rc[a] for d in fa.get(a, ()) if cc[d]]
            if not opts: return False
            if best is None or len(opts) < len(best[1]):
                best = (('cell', (b, c)), opts)
                if len(opts) == 1: break
            for o in opts: pc.setdefault(o, []).append((b, c))
        if len(best[1]) > 1:
            for pr in freepairs:
                l = pc.get(pr, [])
                if not l: return False
                if len(l) < len(best[1]):
                    best = (('pair', pr), l)
        kind, x = best[0]
        for y in best[1]:
            (b, c), (a, d) = (x, y) if kind == 'cell' else (y, x)
            rowcnt[b][a] -= 1; colcnt[c][d] -= 1
            freecells.discard((b, c)); freepairs.discard((a, d)); sol[(b, c)] = (a, d)
            if rec(): return True
            rowcnt[b][a] += 1; colcnt[c][d] += 1
            freecells.add((b, c)); freepairs.add((a, d)); del sol[(b, c)]
        return False
    ok = rec()
    return (dict(sol) if ok else None), nodes[0]

def verify(A, B, n1, k1, n2, k2, sol):
    import collections
    pairs = collections.Counter(sol.values())
    if len(pairs) != n1 * k2 or any(v != 1 for v in pairs.values()): return False
    for a in range(n1):
        for b in range(k1):
            if sum(1 for c in range(n2) if sol[(b, c)][0] == a) != A[a][b]: return False
    for c in range(n2):
        for d in range(k2):
            if sum(1 for b in range(k1) if sol[(b, c)][1] == d) != B[c][d]: return False
    return True

def randmat(rows, cols, rs, cs, rng):
    # configuration model: [u,v] of a uniformly random biregular labeled multigraph
    U = [i for i in range(rows) for _ in range(rs)]
    V = [j for j in range(cols) for _ in range(cs)]
    rng.shuffle(V)
    M = [[0] * cols for _ in range(rows)]
    for i, j in zip(U, V): M[i][j] += 1
    return tuple(tuple(r) for r in M)

def extmat(rows, cols, rs, cs, rng):
    # random vertex-like (northwest-corner with random orders) transportation matrix
    R = [rs] * rows; C = [cs] * cols
    M = [[0] * cols for _ in range(rows)]
    cells = [(i, j) for i in range(rows) for j in range(cols)]; rng.shuffle(cells)
    for i, j in cells:
        x = min(R[i], C[j]); M[i][j] += x; R[i] -= x; C[j] -= x
    return tuple(tuple(r) for r in M)

if __name__ == '__main__' and sys.argv[1] in ('random', 'extreme', 'mixed'):
    import random
    n1, k1, n2, k2, trials, seed = map(int, sys.argv[2:8])
    rng = random.Random(seed); bad = 0; und = 0; maxn = 0
    gA = {'random': randmat, 'extreme': extmat, 'mixed': extmat}[sys.argv[1]]
    gB = {'random': randmat, 'extreme': extmat, 'mixed': randmat}[sys.argv[1]]
    for t in range(trials):
        A = gA(n1, k1, k2, n2, rng); B = gB(n2, k2, k1, n1, rng)
        try:
            s, nodes = solve_mrv(A, B, n1, k1, n2, k2, limit=20000)
        except Undecided:
            und += 1; print('UNDECIDED', A, B, flush=True); continue
        maxn = max(maxn, nodes)
        if s is None: bad += 1; print('NO SOLUTION', A, B, flush=True)
        else: assert verify(A, B, n1, k1, n2, k2, s)
    print('random', (n1, k1, n2, k2), 'trials', trials, 'seed', seed, 'infeasible', bad, 'undecided', und, 'max nodes', maxn)
    sys.exit(0)

if __name__ == '__main__':
    n1, k1, n2, k2 = map(int, sys.argv[1:5])
    assert n1 * k2 == n2 * k1
    As = classes(n1, k1, k2, n2)
    Bs = classes(n2, k2, k1, n1)
    print('params', (n1, k1, n2, k2), 'A classes', len(As), 'B classes', len(Bs), flush=True)
    bad = []; tested = 0
    for A in As:
        for B in Bs:
            s = solve(A, B, n1, k1, n2, k2)
            tested += 1
            if s is None:
                bad.append((A, B)); print('NO SOLUTION', A, B, flush=True)
            else:
                assert verify(A, B, n1, k1, n2, k2, s)
    print('tested pairs', tested, 'infeasible', len(bad))
