"""
Exact Grundy solver for the Game of Arrows on status-labelled forests.

Implements Definition 3.3 / Lemma 3.2 of arXiv:2610.15145v1 literally:
  - a position is a forest where every vertex carries a status in {n,i,o,f};
  - a move orients an unmarked edge u->v, legal iff
        (d(u) >= 2 or s(u) in {i,f}) and (d(v) >= 2 or s(v) in {o,f}),
    where d is the degree in the forest; the move deletes the edge and
    updates s(u) <- s(u)*o, s(v) <- s(v)*i with the table from Lemma 3.2.
  - the game value of a position is the xor of the values of its connected
    components (Proposition 3.7); we memoise on canonical component forms.

No paper theorem is *assumed* inside the recursion: only Lemma 3.2's local
rule (read from the source) is used.  Canonicalisation identifies components
up to isomorphism and up to the global arrow reversal i<->o (both are game
isomorphisms; the reversal invariance is cross-checked in validate.py).

Memory discipline: the memo dict is capped; when the cap is hit we clear it
(correctness is unaffected, only speed).  All entry counts are logged.
"""
from collections import deque

MERGE_OUT = {0: 2, 1: 3, 2: 2, 3: 3}   # s . o   (n->o, i->f, o->o, f->f)
MERGE_IN = {0: 1, 1: 1, 2: 3, 3: 3}    # s . i   (n->i, i->i, o->f, f->f)


def _rooted(adj, status, root, parent):
    ch = []
    for c in adj[root]:
        if c != parent:
            ch.append(_rooted(adj, status, c, root))
    ch.sort()
    return (status[root], tuple(ch))


def _swap(status):
    return tuple(1 if s == 2 else (2 if s == 1 else s) for s in status)


def _centers(adj):
    """Tree centre(s) via the diameter path (isomorphism-invariant)."""
    n = len(adj)
    if n == 1:
        return [0]

    def bfs(s):
        dist = [-1] * n
        par = [-1] * n
        dist[s] = 0
        q = deque([s])
        far = s
        while q:
            x = q.popleft()
            if dist[x] > dist[far]:
                far = x
            for y in adj[x]:
                if dist[y] < 0:
                    dist[y] = dist[x] + 1
                    par[y] = x
                    q.append(y)
        return far, dist, par

    u, _, _ = bfs(0)
    v, dist, par = bfs(u)
    path = []
    x = v
    while x != -1:
        path.append(x)
        x = par[x]
    L = len(path)
    if L % 2 == 1:
        return [path[L // 2]]
    return [path[L // 2 - 1], path[L // 2]]


def canon(n, edges, status):
    """Canonical form of one status-labelled tree component.

    Returns a tagged tuple:
      (0, rooted_form)                for a 1-centre tree (or single vertex)
      (1, rooted_a, rooted_b) sorted  for a 2-centre tree
    identified up to isomorphism and up to the global i<->o reversal.
    """
    adj = [[] for _ in range(n)]
    for u, v in edges:
        adj[u].append(v)
        adj[v].append(u)
    cs = _centers(adj)
    st2 = _swap(status)
    if len(cs) == 1:
        c = cs[0]
        f1 = (0, _rooted(adj, status, c, -1))
        f2 = (0, _rooted(adj, st2, c, -1))
        return min(f1, f2)
    c1, c2 = cs
    a = (1, _rooted(adj, status, c1, c2), _rooted(adj, status, c2, c1))
    if a[1] > a[2]:
        a = (1, a[2], a[1])
    b = (1, _rooted(adj, st2, c1, c2), _rooted(adj, st2, c2, c1))
    if b[1] > b[2]:
        b = (1, b[2], b[1])
    return min(a, b)


def decode(form):
    """Inverse of canon (any representative). Returns (n, edges, status)."""
    edges = []
    status = []

    def build_rooted(t):
        idx = len(status)
        status.append(t[0])
        for ch in t[1]:
            ci = build_rooted(ch)
            edges.append((idx, ci))
        return idx

    if form[0] == 0:
        build_rooted(form[1])
    else:
        i1 = build_rooted(form[1])
        i2 = build_rooted(form[2])
        edges.append((i1, i2))
    return len(status), edges, status


class Solver:
    def __init__(self, cap=2_000_000):
        self.memo = {}
        self.cap = cap
        self.clears = 0
        self.maxsize = 0

    def g(self, form):
        """Exact Grundy value of one component given in canonical form."""
        if form[0] == 0 and not form[1][1]:
            return 0  # isolated vertex
        memo = self.memo
        v = memo.get(form)
        if v is not None:
            return v
        n, edges, status = decode(form)
        opts = set()
        m = len(edges)
        adj = [[] for _ in range(n)]
        for idx, (u, w) in enumerate(edges):
            adj[u].append((w, idx))
            adj[w].append((u, idx))
        for idx in range(m):
            u, w = edges[idx]
            for t, h in ((u, w), (w, u)):
                if not ((len(adj[t]) >= 2 or status[t] in (1, 3)) and
                        (len(adj[h]) >= 2 or status[h] in (2, 3))):
                    continue
                st = list(status)
                st[t] = MERGE_OUT[st[t]]
                st[h] = MERGE_IN[st[h]]
                # split into the two sides; option value is the xor
                sides = []
                for root in (t, h):
                    # BFS from root avoiding the deleted edge
                    comp = []
                    seen = [False] * n
                    seen[root] = True
                    stack = [root]
                    while stack:
                        x = stack.pop()
                        comp.append(x)
                        for y, ei in adj[x]:
                            if ei == idx:
                                continue
                            if not seen[y]:
                                seen[y] = True
                                stack.append(y)
                    idxmap = {x: i for i, x in enumerate(comp)}
                    sub_edges = []
                    for x in comp:
                        for y, ei in adj[x]:
                            if ei != idx and idxmap[y] > idxmap[x]:
                                sub_edges.append((idxmap[x], idxmap[y]))
                    sub_status = [st[x] for x in comp]
                    sub_n = len(comp)
                    if sub_n == 1:
                        sides.append(0)
                    else:
                        sides.append(self.g(canon(sub_n, sub_edges, sub_status)))
                opts.add(sides[0] ^ sides[1])
                if len(memo) > self.cap:
                        memo.clear()
                        self.clears += 1
        val = 0
        while val in opts:
            val += 1
        if len(memo) <= self.cap:
            memo[form] = val
            if len(memo) > self.maxsize:
                self.maxsize = len(memo)
        return val

    def g_position(self, components):
        """components: list of (n, edges, status); returns xor of values."""
        x = 0
        for n, edges, status in components:
            if n == 0 or not edges:
                continue
            x ^= self.g(canon(n, edges, status))
        return x


def piece_status(n, edges):
    """Status vector for an abstract piece: leaves f(3), others n(0)."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    return tuple(3 if deg[i] == 1 else 0 for i in range(n))


def g_piece(solver, n, edges):
    return solver.g(canon(n, edges, piece_status(n, edges)))


def tree_pieces(n, edges):
    """Pieces of a tree T (empty position): delete pendant edges, cut at
    special vertices (adjacent to a leaf) by exploding them into one f-vertex
    per remaining incident edge.  Returns a list of components
    (n_i, edges_i, status_i).  Mirrors Definition 3.6 / Corollary 3.8's
    description; the game value is the xor over components."""
    deg = [0] * n
    for u, v in edges:
        deg[u] += 1
        deg[v] += 1
    is_leaf = [deg[i] == 1 for i in range(n)]
    special = set()
    for u, v in edges:
        if is_leaf[u]:
            special.add(v)
        if is_leaf[v]:
            special.add(u)
    label = {}

    def vid(v, slot):
        return label.setdefault((v, slot), len(label))

    pedges = []
    for i, (u, v) in enumerate(edges):
        if is_leaf[u] or is_leaf[v]:
            continue
        pedges.append((vid(u, i if u in special else -1),
                       vid(v, i if v in special else -1)))
    N = len(label)
    status = [0] * N
    for (v, slot), idx in label.items():
        status[idx] = 3 if slot != -1 else 0
    # connected components
    adj = [[] for _ in range(N)]
    for idx, (u, v) in enumerate(pedges):
        adj[u].append((v, idx))
        adj[v].append((u, idx))
    seen = [False] * N
    comps = []
    for s0 in range(N):
        if seen[s0] or not adj[s0]:
            continue
        stack = [s0]
        seen[s0] = True
        vert = []
        while stack:
            x = stack.pop()
            vert.append(x)
            for y, _ in adj[x]:
                if not seen[y]:
                    seen[y] = True
                    stack.append(y)
        idxmap = {x: i for i, x in enumerate(vert)}
        ce = [(idxmap[a], idxmap[b]) for a, b in pedges
              if idxmap.get(a) is not None and idxmap.get(b) is not None
              and a in idxmap and b in idxmap]
        ce = []
        for a, b in pedges:
            if a in idxmap and b in idxmap:
                ce.append((idxmap[a], idxmap[b]))
        comps.append((len(vert), ce, tuple(status[x] for x in vert)))
    return comps


def g_tree(solver, n, edges):
    """Grundy value of the empty position on tree (n, edges)."""
    x = 0
    for (ni, ei, si) in tree_pieces(n, edges):
        if ei:
            x ^= solver.g(canon(ni, ei, si))
    return x
