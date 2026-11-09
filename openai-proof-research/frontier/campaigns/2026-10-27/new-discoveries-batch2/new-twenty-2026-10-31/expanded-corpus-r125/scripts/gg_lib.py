# gamma_g-perfect graphs (Bujtas-Irsic-Klavzar, arXiv:1908.09513). Graphs: n, adj = list of open-neighbourhood bitmasks.
from functools import lru_cache
def bits(m):
    while m:
        b = m & -m; yield b.bit_length()-1; m ^= b
def popc(m): return bin(m).count('1')
def components(adj, mask):
    out = []
    rem = mask
    while rem:
        s = rem & -rem; comp = s; frontier = s
        while frontier:
            nf = 0
            for x in bits(frontier): nf |= adj[x]
            nf &= mask & ~comp
            comp |= nf; frontier = nf
        out.append(comp); rem &= ~comp
    return out
def is_clique(adj, m):
    for x in bits(m):
        if (adj[x] | (1 << x)) & m != m: return False
    return True
def recog_perfect(adj, mask):
    """Recognizer from Thm (recognition) of the source: strip complete components; at most one non-complete
    component H; v of max degree in the twin-contraction of H; V(H)-N[v] must be a PSC in H-v; recurse on H-v."""
    while True:
        comps = components(adj, mask)
        nc = [c for c in comps if not is_clique(adj, c)]
        if not nc: return True
        if len(nc) > 1: return False
        H = nc[0]
        cl = {x: (adj[x] | (1 << x)) & H for x in bits(H)}
        best = -1; v = -1
        # degree of x-hat in H-hat = number of twin classes (other than own) inside N(x)
        for x in bits(H):
            Nx = cl[x]; seen = set(); own = Nx  # classes adjacent
            d = 0
            for y in bits(Nx & ~(1 << x)):
                c = cl[y]
                if c == cl[x]: continue  # true twin of x
                if c not in seen: seen.add(c); d += 1
            if d > best: best = d; v = x
        Hv = H & ~(1 << v)
        R = H & ~cl[v]
        if R:
            Q = components(adj, R)
            Nv = {}
            for q in Q:
                if not is_clique(adj, q): return False
                rep = None
                for x in bits(q):
                    c = (adj[x] | (1 << x)) & Hv
                    if rep is None: rep = c
                    elif c != rep: return False
                Nv[q] = rep & ~q
            if len(Q) >= 2:
                for i in range(len(Q)):
                    for j in range(i+1, len(Q)):
                        a, b = Nv[Q[i]], Nv[Q[j]]
                        if a == 0 or b == 0: return False
                        if a & b: return False
                        if a & Q[j] or b & Q[i]: return False
                        for x in bits(a):
                            if adj[x] & b != b: return False
        mask = Hv
def gamma(adj, mask):
    vs = list(bits(mask)); cl = [(adj[x] | (1 << x)) & mask for x in vs]
    if not vs: return 0
    from itertools import combinations
    for k in range(1, len(vs)+1):
        for c in combinations(range(len(vs)), k):
            m = 0
            for i in c: m |= cl[i]
            if m == mask: return k
def gamma_g(adj, mask):
    vs = list(bits(mask)); cl = [(adj[x] | (1 << x)) & mask for x in vs]
    @lru_cache(maxsize=None)
    def val(D, dom):
        if D == mask: return 0
        res = None
        for c in cl:
            if c & ~D:
                r = 1 + val(D | c, not dom)
                if res is None or (dom and r < res) or ((not dom) and r > res): res = r
        return res
    return val(0, True)
def brute_perfect(adj, mask):
    # every induced subgraph F (nonempty) satisfies gamma_g(F) == gamma(F)
    sub = mask
    while sub:
        if gamma_g(adj, sub) != gamma(adj, sub): return False
        sub = (sub - 1) & mask
    return True
def imperfect_top(adj, n):
    """Is G (full vertex set) NOT a gamma_g-graph, assuming gamma(G)=2 needed: returns True iff gamma(G)=2 and no
    vertex v with V-N[v] a nonempty homogeneous clique (equivalent to gamma_g = 3 when gamma = 2)."""
    full = (1 << n) - 1
    cl = [adj[x] | (1 << x) for x in range(n)]
    for v in range(n):
        if cl[v] == full: return False  # gamma=1
    ok2 = any(cl[a] | cl[b] == full for a in range(n) for b in range(a+1, n))
    if not ok2: return None  # gamma>=3: undecided by this test
    for v in range(n):
        R = full & ~cl[v]
        x = (R & -R).bit_length()-1
        if all(cl[y] == cl[x] for y in bits(R)) and cl[x] & R == R: return False
    return True
# ---------- canonical form with twin pruning ----------
def refine(adj, n, cells):
    cells = [list(c) for c in cells]
    changed = True
    while changed:
        changed = False
        new = []
        for idx, c in enumerate(cells):
            if len(c) == 1: new.append(c); continue
            masks = []
            for cc in cells:
                m = 0
                for y in cc: m |= 1 << y
                masks.append(m)
            key = {x: tuple(popc(adj[x] & m) for m in masks) for x in c}
            groups = {}
            for x in c: groups.setdefault(key[x], []).append(x)
            if len(groups) > 1:
                changed = True
                for k in sorted(groups): new.append(groups[k])
                new.extend(cells[idx+1:])
                cells = new
                break
            new.append(c)
        else:
            cells = new
    return cells
def canon(adj, n):
    deg = {}
    for x in range(n): deg.setdefault(popc(adj[x]), []).append(x)
    start = refine(adj, n, [deg[k] for k in sorted(deg)])
    best = [None]
    cl = [adj[x] | (1 << x) for x in range(n)]
    def rec(cells):
        if all(len(c) == 1 for c in cells):
            order = [c[0] for c in cells]
            pos = {v: i for i, v in enumerate(order)}
            code = tuple(sorted(sum(1 << pos[y] for y in bits(adj[x])) for x in order))
            code = tuple(sum(1 << pos[y] for y in bits(adj[order[i]])) for i in range(n))
            if best[0] is None or code > best[0]: best[0] = code
            return
        i = min((k for k, c in enumerate(cells) if len(c) > 1), key=lambda k: len(cells[k]))
        tried = []
        for x in cells[i]:
            if any(adj[x] & ~(1 << t) == adj[t] & ~(1 << x) for t in tried): continue  # true or false twin
            tried.append(x)
            nc = cells[:i] + [[x], [y for y in cells[i] if y != x]] + cells[i+1:]
            rec(refine(adj, n, nc))
    rec(start)
    return (n,) + best[0]
def from_code(code):
    n = code[0]; return n, list(code[1:])
