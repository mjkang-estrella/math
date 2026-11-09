"""MathDB 382066 (Muecksch-Roehrle-Tran Conjecture 6.20): strongly chordal G => A_G flag-accurate.
Combinatorial reformulation used (graphic arrangements; Stanley/Edelman-Reiner: A_G free iff G chordal,
exponents = numbers of earlier neighbours along a perfect elimination ordering; restriction to the flat of a
connected partition = graphic arrangement of the simple quotient graph; flags of flats = contraction sequences):
  flagacc(G) iff |V|=1, or there is an edge e with G/e chordal, exp(G/e) = exp(G) minus one copy of max(exp G),
  and flagacc(G/e).
Generation: connected strongly chordal graphs on n vertices from those on n-1 by adding a vertex adjacent to a
nonempty clique (every strongly chordal graph has a simple, hence simplicial, vertex whose deletion keeps it
strongly chordal), deduplicated up to isomorphism (invariant hash + backtracking isomorphism test).
Usage: sc_flag.py NMAX OUTPREFIX   (writes OUTPREFIX-n.txt edge lists; never overwrites)"""
import sys, itertools, pathlib
NMAX = int(sys.argv[1]); OUT = sys.argv[2]

def nbrs(n, E):
    A = [0] * n
    for i, j in E: A[i] |= 1 << j; A[j] |= 1 << i
    return A
def popc(x): return bin(x).count('1')
def peo_exps(n, A):
    """Return sorted exponent list if chordal else None (greedy simplicial elimination)."""
    alive = (1 << n) - 1; ex = []
    while alive:
        for v in range(n):
            if alive >> v & 1:
                N = A[v] & alive
                if all(((A[u] | (1 << u)) & N) == N for u in range(n) if N >> u & 1):
                    ex.append(popc(N)); alive &= ~(1 << v); break
        else:
            return None
    return sorted(ex)
def strongly_chordal(n, A):
    alive = (1 << n) - 1
    if peo_exps(n, A) is None: return False
    while alive:
        for v in range(n):
            if not alive >> v & 1: continue
            N = A[v] & alive
            cl = [((A[u] & alive) | (1 << u)) for u in range(n) if (N | (1 << v)) >> u & 1]
            if all((a & b) == a or (a & b) == b for a, b in itertools.combinations(cl, 2)):
                alive &= ~(1 << v); break
        else:
            return False
    return True
def inv(n, A):
    col = [popc(A[v]) for v in range(n)]
    for _ in range(3):
        col = [hash((col[v], tuple(sorted(col[u] for u in range(n) if A[v] >> u & 1)))) for v in range(n)]
    return col
def key(n, A):
    return (n, sum(popc(a) for a in A), tuple(sorted(inv(n, A))))
def iso(n, A, B, ca=None, cb=None):
    ca = ca or inv(n, A); cb = cb or inv(n, B)
    if sorted(ca) != sorted(cb): return False
    order = sorted(range(n), key=lambda v: (sum(1 for w in range(n) if ca[w] == ca[v]), v))
    m = {}; used = set()
    def bt(i):
        if i == n: return True
        v = order[i]
        for w in range(n):
            if w in used or cb[w] != ca[v]: continue
            if all(((A[v] >> u) & 1) == ((B[w] >> m[u]) & 1) for u in m):
                m[v] = w; used.add(w)
                if bt(i + 1): return True
                del m[v]; used.discard(w)
        return False
    return bt(0)
class Store:
    def __init__(s): s.d = {}
    def find(s, n, A):
        k = key(n, A); c = inv(n, A)
        for (B, cb, val) in s.d.get(k, []):
            if iso(n, A, B, c, cb): return val, True
        return None, False
    def add(s, n, A, val):
        s.d.setdefault(key(n, A), []).append((A, inv(n, A), val))
memo = Store()
def contract(n, A, i, j):
    # merge j into i, relabel to 0..n-2
    m = [k for k in range(n) if k != j]
    idx = {v: t for t, v in enumerate(m)}
    B = [0] * (n - 1)
    for v in range(n):
        for u in range(n):
            if A[v] >> u & 1:
                a = i if v == j else v; b = i if u == j else u
                if a != b:
                    B[idx[a]] |= 1 << idx[b]
    return B
def flagacc(n, A):
    if n == 1: return True
    val, ok = memo.find(n, A)
    if ok: return val
    ex = peo_exps(n, A)
    res = False
    if ex is not None:
        target = ex[:-1]
        seen = set()
        for i in range(n):
            for j in range(i + 1, n):
                if not A[i] >> j & 1: continue
                B = contract(n, A, i, j)
                kB = key(n - 1, B)
                if kB in seen and False: continue
                eB = peo_exps(n - 1, B)
                if eB is None or eB != target: continue
                if flagacc(n - 1, B): res = True; break
            if res: break
    memo.add(n, A, res)
    return res
def cliques(n, A):
    out = []
    def rec(c, cand):
        if c: out.append(c)
        for v in range(n):
            if cand >> v & 1 and (not c or v > max(c)):
                rec(c + [v], cand & A[v])
    rec([], (1 << n) - 1)
    return out
if OUT == 'CONTROL':
    # Source Prop. 6.10 / Remark 6.7 controls: Q_l(M) = inner K_l plus m_ij outer triangles on edge ij.
    def Q(l, M):
        E = [(i, j) for i in range(l) for j in range(i + 1, l)]; n = l
        for (i, j), m in zip([(i, j) for i in range(l) for j in range(i + 1, l)], M):
            for _ in range(m): E += [(i, n), (j, n)]; n += 1
        return n, nbrs(n, E)
    for l, M, expect in [(4, [1] * 6, 'not flag-accurate (Prop 6.10, k=1)'), (4, [2] * 6, 'not flag-accurate (Prop 6.10, k=2)'),
                         (3, [1, 1, 1], 'flag-accurate (3-sun, Cor 6.9)'), (4, [1, 0, 0, 1, 0, 1], 'flag-accurate (4-sun, Cor 6.9)'),
                         (3, [2, 3, 1], 'Q3 family')]:
        n, A = Q(l, M)
        print('control Q', l, M, 'n', n, 'exps', peo_exps(n, A), 'strongly chordal', strongly_chordal(n, A),
              'flagacc', flagacc(n, A), '| source:', expect, flush=True)
    sys.exit(0)
level = [(1, [0])]
for n in range(2, NMAX + 1):
    st = Store(); new = []
    for (m, A) in level:
        for c in cliques(m, A):
            B = A[:] + [0]
            for v in c: B[v] |= 1 << m; B[m] |= 1 << v
            if st.find(m + 1, B)[1]: continue
            if not strongly_chordal(m + 1, B): continue
            st.add(m + 1, B, True); new.append((m + 1, B))
    level = new
    bad = [B for (m, B) in level if not flagacc(m, B)]
    p = pathlib.Path(f'{OUT}-{n}.txt')
    if not p.exists():
        with open(p, 'w') as f:
            for (m, B) in level:
                f.write(' '.join(f'{i}-{j}' for i in range(m) for j in range(i + 1, m) if B[i] >> j & 1) + '\n')
    print('n', n, 'connected strongly chordal (up to iso)', len(level), 'NOT flag-accurate', len(bad), flush=True)
    for B in bad[:5]:
        print('   counterexample edges', [(i, j) for i in range(n) for j in range(i + 1, n) if B[i] >> j & 1], flush=True)
