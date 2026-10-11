"""I166 independent standard-library toolkit for cubic bipartite planar graphs.

Written from scratch for the I166 audit/research task.  No I164/I165 module
is imported or executed anywhere in this directory.  Graphs are represented
by oriented face lists: every undirected edge must appear exactly once in
each direction across the face list (a combinatorial oriented closed
surface).  All enumeration and linear algebra is exact.
"""
from collections import Counter, deque
from fractions import Fraction
from itertools import combinations


# ---------------------------------------------------------------- basics

def ue(a, b):
    return (a, b) if a < b else (b, a)


def face_edges(faces):
    """Sorted unique undirected edge list implied by a face list."""
    out = set()
    for f in faces:
        for a, b in zip(f, f[1:] + f[:1]):
            out.add(ue(a, b))
    return sorted(out)


def neighbor_map(edges):
    nb = {}
    for a, b in edges:
        nb.setdefault(a, set()).add(b)
        nb.setdefault(b, set()).add(a)
    return {v: sorted(nb[v]) for v in sorted(nb)}


def orient_faces(faces):
    """Flip some face cycles so every edge occurs once in each direction.

    The two darts of every edge are paired; flips propagate across adjacent
    faces; consistency and the oriented-dart condition are verified.
    """
    faces = [tuple(f) for f in faces]
    dart_owner = {}
    for i, f in enumerate(faces):
        for a, b in zip(f, f[1:] + f[:1]):
            dart_owner.setdefault(ue(a, b), []).append((i, a < b))
    if any(len(v) != 2 for v in dart_owner.values()):
        raise ValueError("not a closed surface: edge incidence != 2")
    adj = {}
    for (i, di), (j, dj) in dart_owner.values():
        adj.setdefault(i, []).append((j, di == dj))
        adj.setdefault(j, []).append((i, di == dj))
    flip = {0: False}
    queue = deque([0])
    while queue:
        i = queue.popleft()
        for j, same in adj.get(i, ()):
            want = flip[i] ^ same
            if j in flip:
                if flip[j] != want:
                    raise ValueError("non-orientable face list")
            else:
                flip[j] = want
                queue.append(j)
    if len(flip) != len(faces):
        raise ValueError("disconnected face list")
    out = [list(reversed(f)) if flip[i] else list(f) for i, f in enumerate(faces)]
    darts = Counter()
    for f in out:
        for a, b in zip(f, f[1:] + f[:1]):
            darts[(a, b)] += 1
    for (a, b) in face_edges(out):
        if darts[(a, b)] != 1 or darts[(b, a)] != 1:
            raise ValueError("orientation failed")
    return out


def prism_faces(m):
    """Even circular ladder L_m: two m-cycles joined by m rungs."""
    if m < 4 or m % 2:
        raise ValueError("need even m >= 4")
    top = list(range(m))
    bot = list(range(m, 2 * m))
    sides = [[i, (i + 1) % m, m + (i + 1) % m, m + i] for i in range(m)]
    return orient_faces([top, bot] + sides)


def cube_faces():
    """The cube Q3 as oriented faces, vertices as 3-bit integers 0..7."""
    def v(x, y, z):
        return x + 2 * y + 4 * z
    faces = [
        [v(0, 0, 0), v(1, 0, 0), v(1, 1, 0), v(0, 1, 0)],
        [v(0, 0, 1), v(1, 0, 1), v(1, 1, 1), v(0, 1, 1)],
        [v(0, 0, 0), v(1, 0, 0), v(1, 0, 1), v(0, 0, 1)],
        [v(0, 1, 0), v(1, 1, 0), v(1, 1, 1), v(0, 1, 1)],
        [v(0, 0, 0), v(0, 1, 0), v(0, 1, 1), v(0, 0, 1)],
        [v(1, 0, 0), v(1, 1, 0), v(1, 1, 1), v(1, 0, 1)],
    ]
    return orient_faces(faces)


def is_connected(nb, skip=frozenset()):
    vs = [v for v in nb if v not in skip]
    if not vs:
        return True
    seen = {vs[0]}
    stack = [vs[0]]
    while stack:
        for w in nb[stack.pop()]:
            if w not in seen and w not in skip:
                seen.add(w)
                stack.append(w)
    return len(seen) == len(vs)


def certify(faces):
    """Full class certificate; raises AssertionError on any violation.

    Checks: faces are simple cycles of length >= 4; the oriented face list
    is a consistent closed surface with a single link at each vertex; the
    graph is simple, cubic, connected, bipartite; Euler characteristic two;
    every deletion of <= 2 vertices stays connected.  Returns a summary.
    """
    es = face_edges(faces)
    nb = neighbor_map(es)
    n = len(nb)
    assert all(len(f) == len(set(f)) >= 4 for f in faces), "bad face"
    assert all(len(nb[v]) == 3 for v in nb), "not cubic"
    assert len(es) * 2 == 3 * n, "edge count"
    rotation = {}
    for v in nb:
        suc = {}
        for f in faces:
            if v in f:
                j = f.index(v)
                suc[f[j - 1]] = f[(j + 1) % len(f)]
        assert set(suc) == set(nb[v]), "link is not a single cycle"
        a = nb[v][0]
        assert suc[suc[suc[a]]] == a and suc[a] != a
        rotation[v] = (a, suc[a], suc[suc[a]])
    assert n - len(es) + len(faces) == 2, "Euler characteristic != 2"
    color = {}
    for s in nb:
        if s in color:
            continue
        color[s] = 0
        queue = deque([s])
        while queue:
            a = queue.popleft()
            for b in nb[a]:
                if b not in color:
                    color[b] = 1 - color[a]
                    queue.append(b)
                assert color[b] != color[a], "odd cycle"
    assert is_connected(nb), "disconnected"
    deletions = 0
    for k in (1, 2):
        for cut in combinations(nb, k):
            assert is_connected(nb, frozenset(cut)), ("cut", cut)
            deletions += 1
    return {"n": n, "m": len(es), "faces": len(faces),
            "bipartition_sizes": sorted(Counter(color.values()).values()),
            "deletion_pairs_checked": deletions, "rotation": rotation,
            "color": color}


# ---------------------------------------------------------------- operations

def square_expand(faces, fi, i, j):
    """Replace face edges f[i]-f[i+1] and f[j]-f[j+1] by a square insert.

    The two edges must be distinct edges of face fi whose indices differ by
    an even number >= 2 (both residual boundary paths are then odd).  Four
    new vertices p,q,r,s are added: u-p-q-v and x-r-s-y paths replace the
    removed edges u-v and x-y, and p-q-s-r is a new square face.
    Returns (new_faces, (u, v, x, y)).
    """
    f = faces[fi]
    L = len(f)
    assert 0 <= i < j < L and (j - i) % 2 == 0 and j - i >= 2
    u, v, x, y = f[i], f[(i + 1) % L], f[j], f[(j + 1) % L]
    assert len({u, v, x, y}) == 4, "terminals not distinct"
    p0 = max(neighbor_map(face_edges(faces))) + 1
    p, q, r, s = p0, p0 + 1, p0 + 2, p0 + 3
    sub = {(u, v): (p, q), (v, u): (q, p), (x, y): (s, r), (y, x): (r, s)}
    out = []
    for k, face in enumerate(faces):
        if k == fi:
            continue
        row = []
        for a, b in zip(face, face[1:] + face[:1]):
            if (a, b) in sub:
                row.extend((a,) + sub[(a, b)])
            else:
                row.append(a)
        out.append(row)
    out.append(f[i + 1:j + 1] + [s, q])
    out.append(f[j + 1:] + f[:i + 1] + [p, r])
    out.append([p, q, s, r])
    return orient_faces(out), (u, v, x, y)


def admissible_steps(faces):
    """All square-expansion steps: unordered face-edge pairs, odd residuals."""
    for fi, f in enumerate(faces):
        L = len(f)
        for i in range(L):
            for j in range(i + 2, L):
                if (j - i) % 2 == 0:
                    yield fi, i, j


def splice_faces(faces1, v, faces2, w, port_map):
    """Delete v and w, join their neighbors pairwise (GSW splice).

    port_map: dict from each neighbor of v to a neighbor of w.
    Returns (new_faces, relabel2).
    """
    nb1 = neighbor_map(face_edges(faces1))
    nb2 = neighbor_map(face_edges(faces2))
    assert set(port_map) == set(nb1[v]) and set(port_map.values()) == set(nb2[w])
    shift = max(nb1) + 1
    relabel2 = {x: shift + k for k, x in enumerate(sorted(nb2))}
    out = [f[:] for f in faces1 if v not in f]
    for f in faces2:
        if w not in f:
            out.append([relabel2[x] for x in f])
    for f in faces1:
        if v not in f:
            continue
        j = f.index(v)
        arc = f[j + 1:] + f[:j]          # open walk from v around the face
        left, right = port_map[arc[-1]], port_map[arc[0]]
        match = None
        for g in faces2:
            if w not in g:
                continue
            k = g.index(w)
            garc = g[k + 1:] + g[:k]
            if {garc[0], garc[-1]} == {left, right}:
                cand = garc if garc[0] == left else garc[::-1]
                assert match is None, "ambiguous partner face"
                match = cand
        assert match is not None, "no partner face"
        out.append(arc + [relabel2[x] for x in match])
    return orient_faces(out), relabel2


def cube_expand_vertex(faces, v):
    """Replace vertex v by the 7-vertex gadget Q3 minus a vertex (n -> n+6),
    implemented as a splice with the cube."""
    cube = cube_faces()
    nb_c = neighbor_map(face_edges(cube))
    nb_g = neighbor_map(face_edges(faces))
    port_map = {a: b for a, b in zip(sorted(nb_g[v]), sorted(nb_c[0]))}
    out, _ = splice_faces(faces, v, cube, 0, port_map)
    return out


# ---------------------------------------------------------------- enumeration

def hamilton_cycles_dfs(edges, visit_cap=None):
    """Anchored vertex-path DFS with necessary-pruning; unoriented edge sets.

    Root at the smallest vertex; each cycle is emitted once via the
    second-vertex < last-vertex rule.  A partial path is pruned only when a
    condition necessary for every completion fails: some unused vertex
    cannot keep two usable incident edges, the root loses its closing
    option, or the usable subgraph disconnects from the tip.
    Returns (set of frozensets, exhausted_flag).
    """
    nb = neighbor_map(edges)
    verts = sorted(nb)
    n = len(verts)
    idx = {v: k for k, v in enumerate(verts)}
    bit = [1 << k for k in range(n)]
    nmask = [0] * n
    for v in verts:
        m = 0
        for w in nb[v]:
            m |= bit[idx[w]]
        nmask[idx[v]] = m
    full = (1 << n) - 1
    root = 0
    out = set()
    state = {"visits": 0, "dead": False}
    path_edges = []

    def rec(tip, unused, second):
        if state["dead"]:
            return
        state["visits"] += 1
        if visit_cap is not None and state["visits"] > visit_cap:
            state["dead"] = True
            return
        if unused == 0:
            if nmask[tip] & bit[root] and second < tip:
                out.add(frozenset(path_edges) |
                        {ue(verts[root], verts[tip])})
            return
        usable = unused | bit[tip] | bit[root]
        m = unused
        while m:
            low = m & -m
            k = low.bit_length() - 1
            m ^= low
            if bin(nmask[k] & usable).count("1") < 2:
                return
        if not (nmask[tip] & unused):
            return
        if not (nmask[root] & (unused | bit[tip])):
            return
        seen = bit[tip]
        frontier = bit[tip]
        while frontier:
            acc = 0
            f = frontier
            while f:
                low = f & -f
                k = low.bit_length() - 1
                f ^= low
                acc |= nmask[k]
            acc &= usable & ~seen
            seen |= acc
            frontier = acc
        if seen != usable:
            return
        cand = nmask[tip] & unused
        while cand:
            low = cand & -cand
            k = low.bit_length() - 1
            cand ^= low
            path_edges.append(ue(verts[tip], verts[k]))
            rec(k, unused ^ bit[k], second)
            path_edges.pop()

    cand0 = nmask[root]
    while cand0:
        low = cand0 & -cand0
        k = low.bit_length() - 1
        cand0 ^= low
        path_edges.append(ue(verts[root], verts[k]))
        rec(k, full ^ bit[root] ^ bit[k], verts[k])
        path_edges.pop()
    return out, not state["dead"]


def spanning_paths_pruned(edges, a, b, visit_cap=None):
    """All vertex-spanning a-b paths as edge frozensets, necessary-pruned.

    Same pruning scheme as hamilton_cycles_dfs, with b taking the role of
    the closing endpoint: usable = unused | {tip} | {b}; every unused vertex
    other than b keeps >= 2 usable neighbors, b keeps >= 1; the usable set
    stays connected from the tip.  All conditions are necessary.
    Returns (set of frozensets, exhausted_flag).
    """
    nb = neighbor_map(edges)
    verts = sorted(nb)
    n = len(verts)
    idx = {v: k for k, v in enumerate(verts)}
    bit = [1 << k for k in range(n)]
    nmask = [0] * n
    for v in verts:
        m = 0
        for w in nb[v]:
            m |= bit[idx[w]]
        nmask[idx[v]] = m
    out = set()
    state = {"visits": 0, "dead": False}
    acc = []
    bb = bit[idx[b]]

    def rec(tip, unused):
        if state["dead"]:
            return
        state["visits"] += 1
        if visit_cap is not None and state["visits"] > visit_cap:
            state["dead"] = True
            return
        if verts[tip] == b:
            if unused == 0:
                out.add(frozenset(acc))
            return
        usable = unused | bit[tip]
        m = unused
        while m:
            low = m & -m
            k = low.bit_length() - 1
            m ^= low
            need = 1 if k == bb.bit_length() - 1 else 2
            if bin(nmask[k] & usable).count("1") < need:
                return
        if not (nmask[tip] & unused):
            return
        seen = bit[tip]
        frontier = bit[tip]
        while frontier:
            accm = 0
            f = frontier
            while f:
                low = f & -f
                k = low.bit_length() - 1
                f ^= low
                accm |= nmask[k]
            accm &= usable & ~seen
            seen |= accm
            frontier = accm
        if seen != usable:
            return
        cand = nmask[tip] & unused
        while cand:
            low = cand & -cand
            k = low.bit_length() - 1
            cand ^= low
            acc.append(ue(verts[tip], verts[k]))
            rec(k, unused ^ bit[k])
            acc.pop()

    rec(idx[a], (1 << n) - 1 - bit[idx[a]])
    return out, not state["dead"]


def perfect_matchings(edges):
    """All perfect matchings by first-vertex branching (exact)."""
    nb = neighbor_map(edges)
    verts = sorted(nb)
    out = []

    def rec(remaining, acc):
        if not remaining:
            out.append(frozenset(acc))
            return
        a = min(remaining)
        for b in nb[a]:
            if b in remaining:
                acc.append(ue(a, b))
                rec(remaining - {a, b}, acc)
                acc.pop()

    rec(set(verts), [])
    return out


def components_of(vertices, edges):
    nb = neighbor_map(edges)
    unseen = set(vertices)
    comps = []
    while unseen:
        s = min(unseen)
        seen = {s}
        stack = [s]
        while stack:
            for w in nb.get(stack.pop(), ()):
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        unseen -= seen
        comps.append(frozenset(seen))
    return comps


def hamilton_cycles_matching(edges):
    """Independent enumerator: perfect matchings with connected complement.

    In a cubic graph the complement of a perfect matching is 2-regular, so
    it is a Hamiltonian cycle iff it is connected.
    """
    nb = neighbor_map(edges)
    verts = sorted(nb)
    es = frozenset(edges)
    out = set()
    for mm in perfect_matchings(edges):
        comp = es - mm
        if len(components_of(verts, sorted(comp))) == 1:
            out.add(comp)
    return out


# ---------------------------------------------------------------- linear algebra

def rank_rows(rows, early_stop=None):
    """Exact rational row rank by Gaussian elimination."""
    piv = {}
    r = 0
    for row in rows:
        row = list(row)
        for j in sorted(piv):
            if row[j]:
                a = row[j]
                prow = piv[j]
                row = [x - a * y for x, y in zip(row, prow)]
        if any(row):
            j = next(k for k, x in enumerate(row) if x)
            a = row[j]
            piv[j] = [x / a for x in row]
            r += 1
            if early_stop is not None and r >= early_stop:
                return r
    return r


def cycle_differences(edges, cycles):
    """Difference rows H - H0 of 0-1 incidence vectors over the edge list."""
    es = list(edges)
    cycles = sorted(cycles, key=lambda h: sorted(h))
    base = cycles[0]
    for h in cycles[1:]:
        yield [Fraction(1 if e in h else 0) - (1 if e in base else 0)
               for e in es]


def face_circulation(face, edges):
    """Alternating +1/-1 circulation around an even face, over the edge list."""
    es = list(edges)
    vec = dict(zip(es, [Fraction(0)] * len(es)))
    for k, (a, b) in enumerate(zip(face, face[1:] + face[:1])):
        vec[ue(a, b)] = Fraction(1 if k % 2 == 0 else -1)
    return [vec[e] for e in es]


# ---------------------------------------------------------------- matching / brace test

def _bipartite_pm_exists(nb, left, right, removed):
    """Kuhn augmenting paths; True iff a perfect matching exists."""
    left = [v for v in left if v not in removed]
    right = set(right) - set(removed)
    if len(left) != len(right):
        return False
    match_r = {}

    def aug(x, seen):
        for y in nb[x]:
            if y in right and y not in seen:
                seen.add(y)
                if y not in match_r or aug(match_r[y], seen):
                    match_r[y] = x
                    return True
        return False

    for a in left:
        if not aug(a, set()):
            return False
    return True


def bipartition(nb):
    color = {}
    for s in sorted(nb):
        if s in color:
            continue
        color[s] = 0
        queue = deque([s])
        while queue:
            a = queue.popleft()
            for b in nb[a]:
                if b not in color:
                    color[b] = 1 - color[a]
                    queue.append(b)
                elif color[b] == color[a]:
                    return None
    return color


def is_brace(edges):
    """Brace test: connected bipartite and 2-extendable (GSW Theorem 2.3).

    Every pair of independent edges must extend to a perfect matching.
    Returns (is_brace, color_dict_or_None).
    """
    nb = neighbor_map(edges)
    verts = sorted(nb)
    color = bipartition(nb)
    if color is None or not is_connected(nb):
        return False, color
    A = [v for v in verts if color[v] == 0]
    B = [v for v in verts if color[v] == 1]
    if len(A) != len(B):
        return False, color
    for e1, e2 in combinations(edges, 2):
        a, b = e1
        c, d = e2
        if len({a, b, c, d}) < 4:
            continue
        if not _bipartite_pm_exists(nb, A, B, {a, b, c, d}):
            return False, color
    return True, color


def _max_flow(nb, source, sink, cap=4):
    """Unit-capacity BFS augmenting flow, capped; returns (value, source_side)."""
    res = {u: {} for u in nb}
    for u in nb:
        for w in nb[u]:
            res[u][w] = res[u].get(w, 0) + 1
    flow = 0
    while flow < cap:
        parent = {source: None}
        queue = deque([source])
        while queue and sink not in parent:
            u = queue.popleft()
            for w, c in res[u].items():
                if c > 0 and w not in parent:
                    parent[w] = u
                    queue.append(w)
        if sink not in parent:
            break
        v = sink
        while parent[v] is not None:
            u = parent[v]
            res[u][v] -= 1
            res[v][u] = res[v].get(u, 0) + 1
            v = u
        flow += 1
    side = {source}
    queue = deque([source])
    while queue:
        u = queue.popleft()
        for w, c in res[u].items():
            if c > 0 and w not in side:
                side.add(w)
                queue.append(w)
    return flow, side


def has_nontrivial_3cut(edges):
    """Nontrivial 3-edge-cut via edge contraction (cross-check of brace test).

    For a cubic 3-edge-connected graph G: if edge (a,b) is contracted to c,
    deg(c) = 4, so the star at c is not a 3-cut.  Any 3-cut of G/e has both
    shores of size >= 2 in G/e iff it gives a nontrivial 3-cut of G (a
    one-vertex shore in G/e is a star of G, detected and ignored).  For each
    edge e and sink t, the minimal source side S_min (residual reachable
    set) is tested: |S_min| >= 2 (automatic, shown in the audit note) and
    |V \\ S_min| >= 2 certify a nontrivial cut.  Completeness: a nontrivial
    3-cut of G persists in G/e for any e inside one shore.
    """
    nb = neighbor_map(edges)
    verts = sorted(nb)
    for a, b in edges:
        cnb = {v: set() for v in verts if v != b}
        for u in nb:
            if u == b:
                continue
            for w in nb[u]:
                x = a if w == b else w
                if x != u:
                    cnb[u].add(x)
                    cnb[x].add(u)
        cnb = {u: sorted(d) for u, d in cnb.items()}
        ncv = len(cnb)
        for t in cnb:
            if t == a:
                continue
            f, side = _max_flow(cnb, a, t, cap=4)
            if f == 3 and len(side) >= 2 and ncv - len(side) >= 2:
                return True
    return False


# ---------------------------------------------------------------- canonical form

def canonical_form(faces):
    """Canonical adjacency signature for a 3-CONNECTED PLANAR graph.

    Uses Whitney uniqueness: the face list determines the rotation system,
    and every isomorphism either preserves all vertex rotations or reverses
    them all.  Rooting the encoding at a single directed edge (dart) plus a
    reflection bit therefore kills all freedom, so the minimum encoding
    over all darts and both reflection choices is a complete isomorphism
    invariant.  Argument: faces (oriented face list), NOT an edge list.
    """
    nb = neighbor_map(face_edges(faces))
    # rotation: rot[(v, u)] = neighbor of v following u in the rotation
    rot = {}
    for f in faces:
        L_ = len(f)
        for k in range(L_):
            rot[(f[k], f[k - 1])] = f[(k + 1) % L_]
    for v in nb:
        ns = nb[v]
        assert len(ns) == 3, "canonical form is implemented for cubic graphs"
        w = ns[0]
        seen = []
        for _ in range(3):
            seen.append(w)
            w = rot[(v, w)]
        assert sorted(seen) == ns and w == ns[0]

    def encode(x, y, flip):
        label = {x: 0, y: 1}
        order = [x, y]
        for v in order:  # order grows during the sweep
            ns = nb[v]
            anchor = min(ns, key=lambda w: label.get(w, 1 << 30))
            seq = []
            w = rot[(v, anchor)]
            while w != anchor:
                seq.append(w)
                w = rot[(v, w)]
            ring = [anchor] + (seq[::-1] if flip else seq)
            for w in ring:
                if w not in label:
                    label[w] = len(label)
                    order.append(w)
        posn = {v: k for k, v in enumerate(order)}
        return tuple(tuple(sorted(posn[w] for w in nb[v])) for v in order)

    best = None
    for a, b in face_edges(faces):
        for d in ((a, b), (b, a)):
            for flip in (False, True):
                code = encode(d[0], d[1], flip)
                if best is None or code < best:
                    best = code
    return best
