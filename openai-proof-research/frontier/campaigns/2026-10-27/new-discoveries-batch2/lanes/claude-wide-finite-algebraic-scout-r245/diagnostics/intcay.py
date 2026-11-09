"""Exploratory search: integral Cay(S_n, T) with G_T not a cograph.

Source: Abdollahi-Arezoomand-Ebrahimi, arXiv:2305.00279v1, Conjecture 1.
Spectrum of Cay(S_n,T) = union over partitions lam of spec(sum_{ij in E} rho_lam((i j))),
rho_lam = Young's orthogonal form.  Floating point screen only; any hit is re-verified
exactly elsewhere.  Usage: intcay.py gen N   |  intcay.py test N [maxedges]
"""
import sys, json, itertools, math, pathlib
import numpy as np

D = pathlib.Path(__file__).resolve().parent


def partitions(n, m=None):
    m = n if m is None else m
    if n == 0:
        yield ()
        return
    for k in range(min(n, m), 0, -1):
        for p in partitions(n - k, k):
            yield (k,) + p


def syt(shape):
    n = sum(shape)
    res = []

    def rec(rows, k, pos):
        if k > n:
            res.append(dict(pos))
            return
        for r in range(len(shape)):
            c = len(rows[r])
            if c < shape[r] and (r == 0 or len(rows[r - 1]) > c):
                rows[r].append(k)
                pos[k] = (r, c)
                rec(rows, k + 1, pos)
                rows[r].pop()
                del pos[k]
    rec([[] for _ in shape], 1, {})
    return res


def irrep_transpositions(shape):
    """Return dict (i,j)->matrix, 1-based i<j, Young orthogonal form."""
    n = sum(shape)
    T = syt(shape)
    key = {tuple(sorted(t.items())): a for a, t in enumerate(T)}
    d = len(T)
    S = {}
    for k in range(1, n):
        M = np.zeros((d, d))
        for a, t in enumerate(T):
            (r1, c1), (r2, c2) = t[k], t[k + 1]
            r = (c2 - r2) - (c1 - r1)
            M[a, a] = 1.0 / r
            if abs(r) > 1:
                u = dict(t)
                u[k], u[k + 1] = t[k + 1], t[k]
                b = key[tuple(sorted(u.items()))]
                M[b, a] = math.sqrt(1 - 1.0 / r ** 2)
        S[k] = M
    P = {}
    for i in range(1, n):
        P[(i, i + 1)] = S[i]
        for j in range(i + 2, n + 1):
            P[(i, j)] = S[j - 1] @ P[(i, j - 1)] @ S[j - 1]
    return P


def is_cograph(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b); adj[b].add(a)
    for a, b, c, d in itertools.permutations(range(n), 4):
        if a < d and b in adj[a] and c in adj[b] and d in adj[c] and c not in adj[a] and d not in adj[a] and d not in adj[b]:
            return False
    return True


def canon(n, adj):
    """Exact canonical form: refine colours, then min over within-cell permutations."""
    col = [len(adj[v]) for v in range(n)]
    while True:
        sig = [(col[v], tuple(sorted(col[u] for u in adj[v]))) for v in range(n)]
        keys = sorted(set(sig))
        new = [keys.index(s) for s in sig]
        if len(set(new)) == len(set(col)):
            col = new
            break
        col = new
    cells = {}
    for v in range(n):
        cells.setdefault(col[v], []).append(v)
    order = [cells[c] for c in sorted(cells)]
    best = None
    for combo in itertools.product(*[itertools.permutations(c) for c in order]):
        perm = [v for cell in combo for v in cell]
        pos = {v: i for i, v in enumerate(perm)}
        code = tuple(sorted((min(pos[a], pos[b]), max(pos[a], pos[b])) for a in range(n) for b in adj[a] if a < b))
        if best is None or code < best:
            best = code
    return best


def gen(n):
    """All graphs on n vertices up to iso with <= floor(C(n,2)/2) edges (complements cover the rest)."""
    half = n * (n - 1) // 4
    level = {tuple(): None}
    out = [()]
    for m in range(half):
        nxt = set()
        for code in level:
            es = set(code)
            for a in range(n):
                for b in range(a + 1, n):
                    if (a, b) not in es:
                        adj = [set() for _ in range(n)]
                        for x, y in es | {(a, b)}:
                            adj[x].add(y); adj[y].add(x)
                        nxt.add(canon(n, adj))
        level = dict.fromkeys(nxt)
        out.extend(sorted(nxt))
        print('edges', m + 1, len(nxt), flush=True)
    (D / f'graphs{n}.json').write_text(json.dumps(out))


def lap_integral(n, edges):
    L = np.zeros((n, n))
    for a, b in edges:
        L[a, a] += 1; L[b, b] += 1; L[a, b] -= 1; L[b, a] -= 1
    ev = np.linalg.eigvalsh(L)
    return np.max(np.abs(ev - np.round(ev))) < 1e-7


def test(n):
    graphs = [tuple(map(tuple, g)) for g in json.loads((D / f"graphs{n}.json").read_text())]
    shapes = [s for s in partitions(n)]
    # rho_{lam'} = sgn (x) rho_lam, so M_{lam'} = -M_lam: keep one of each conjugate pair.
    conj = lambda s: tuple(sum(1 for p in s if p > i) for i in range(s[0]))
    keep = [s for s in shapes if s >= conj(s)]
    reps = {s: irrep_transpositions(s) for s in keep}
    stats = {'graphs': len(graphs), 'lap_integral': 0, 'noncograph_lap_integral': 0, 'hits': []}
    full = n * (n - 1) // 2
    for code in graphs:
        for edges in (code, tuple(e for e in itertools.combinations(range(n), 2) if e not in set(code))):
            if len(edges) * 2 == full and edges != code:
                continue
            if not lap_integral(n, edges):
                continue
            stats['lap_integral'] += 1
            if is_cograph(n, edges):
                continue
            stats['noncograph_lap_integral'] += 1
            worst = 0.0
            for s in keep:
                M = sum(reps[s][(a + 1, b + 1)] for a, b in edges)
                ev = np.linalg.eigvalsh(M)
                worst = max(worst, float(np.max(np.abs(ev - np.round(ev)))))
                if worst > 1e-6:
                    break
            if worst <= 1e-6:
                stats['hits'].append(edges)
                print('HIT', n, edges, flush=True)
    print(json.dumps({k: (v if k != 'hits' else len(v)) for k, v in stats.items()}))
    (D / f'intcay-result{n}.json').write_text(json.dumps(stats))


if __name__ == '__main__' and sys.argv[1] in ('gen', 'test'):
    n = int(sys.argv[2])
    gen(n) if sys.argv[1] == 'gen' else test(n)


def gen_levels(n, lo, hi):
    """Resumable variant: level m stored in graphs{n}-L{m}.json; computes levels lo+1..hi."""
    if lo == 0:
        (D / f'graphs{n}-L0.json').write_text(json.dumps([[]]))
    level = [tuple(map(tuple, g)) for g in json.loads((D / f'graphs{n}-L{lo}.json').read_text())]
    for m in range(lo, hi):
        nxt = set()
        for code in level:
            es = set(code)
            for a in range(n):
                for b in range(a + 1, n):
                    if (a, b) not in es:
                        adj = [set() for _ in range(n)]
                        for x, y in es | {(a, b)}:
                            adj[x].add(y); adj[y].add(x)
                        nxt.add(canon(n, adj))
        level = sorted(nxt)
        (D / f'graphs{n}-L{m + 1}.json').write_text(json.dumps(level))
        print('edges', m + 1, len(level), flush=True)


def merge(n):
    half = n * (n - 1) // 4
    out = []
    for m in range(half + 1):
        out.extend(json.loads((D / f'graphs{n}-L{m}.json').read_text()))
    (D / f'graphs{n}.json').write_text(json.dumps(out))
    print('merged', len(out))


if __name__ == '__main__' and sys.argv[1] == 'levels':
    gen_levels(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
if __name__ == '__main__' and sys.argv[1] == 'merge':
    merge(int(sys.argv[2]))


def test_levels(n, lo, hi):
    """Like test(), but streams level files graphs{n}-L{m}.json for m in [lo, hi]."""
    shapes = list(partitions(n))
    conj = lambda s: tuple(sum(1 for p in s if p > i) for i in range(s[0]))
    keep = [s for s in shapes if s >= conj(s)]
    reps = {s: irrep_transpositions(s) for s in keep}
    full = n * (n - 1) // 2
    stats = {'n': n, 'levels': [lo, hi], 'graphs': 0, 'lap_integral': 0, 'noncograph_lap_integral': 0, 'hits': [], 'checked_noncographs': []}
    for m in range(lo, hi + 1):
        for code in json.loads((D / f'graphs{n}-L{m}.json').read_text()):
            code = tuple(map(tuple, code))
            stats['graphs'] += 1
            for edges in (code, tuple(e for e in itertools.combinations(range(n), 2) if e not in set(code))):
                if len(edges) * 2 == full and edges != code:
                    continue
                if not lap_integral(n, edges):
                    continue
                stats['lap_integral'] += 1
                if is_cograph(n, edges):
                    continue
                stats['noncograph_lap_integral'] += 1
                stats['checked_noncographs'].append(edges)
                worst = 0.0
                for s in keep:
                    M = sum(reps[s][(a + 1, b + 1)] for a, b in edges)
                    ev = np.linalg.eigvalsh(M)
                    worst = max(worst, float(np.max(np.abs(ev - np.round(ev)))))
                    if worst > 1e-6:
                        break
                if worst <= 1e-6:
                    stats['hits'].append(edges)
                    print('HIT', n, edges, flush=True)
    print(json.dumps({k: (v if k not in ('hits', 'checked_noncographs') else len(v)) for k, v in stats.items()}))
    (D / f'intcay-result{n}-L{lo}-{hi}.json').write_text(json.dumps(stats))


if __name__ == '__main__' and sys.argv[1] == 'testlevels':
    test_levels(int(sys.argv[2]), int(sys.argv[3]), int(sys.argv[4]))
