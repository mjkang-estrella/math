"""
Decomposition solver for the Game of Arrows on trees.

A position is a forest of unmarked edges whose vertices carry a label
    'N' : no marked edge at this vertex yet
    'I' : at least one marked edge points IN, none points out
    'O' : at least one marked edge points OUT, none points in
    'F' : free / special -- the vertex can never become a sink or source
          (it already has an in- and an out-edge, or it keeps a dead edge forever)
Orienting the unmarked edge u->v is legal iff
    (deg(u) >= 2 or L(u) in {I,F})  and  (deg(v) >= 2 or L(v) in {O,F}),
where deg is the number of unmarked edges at the vertex.
Normalisation:
    * edges with no legal direction are deleted; their endpoints become F
      (they keep an unmarked edge forever);
    * an F vertex is split into one F leaf per incident edge;
    * isolated vertices are deleted.
The position is the disjunctive sum of its components, so its Grundy value is the
XOR of the component values.  Component values are memoised on a canonical form.
"""
import sys
from functools import lru_cache

sys.setrecursionlimit(1000000)

OUT_AFTER = {'N': 'O', 'I': 'F', 'O': 'O', 'F': 'F'}
IN_AFTER = {'N': 'I', 'I': 'I', 'O': 'F', 'F': 'F'}


def can_tail(lab, deg):
    return deg >= 2 or lab in ('I', 'F')


def can_head(lab, deg):
    return deg >= 2 or lab in ('O', 'F')


def normalise(labels, edges):
    """labels: dict vertex->label ; edges: list of (u,v).
    Returns list of components, each (labels_dict, edge_list), fully normalised."""
    labels = dict(labels)
    edges = list(edges)
    changed = True
    while changed:
        changed = False
        deg = {}
        for u, v in edges:
            deg[u] = deg.get(u, 0) + 1
            deg[v] = deg.get(v, 0) + 1
        keep = []
        for (u, v) in edges:
            ok = (can_tail(labels[u], deg[u]) and can_head(labels[v], deg[v])) or \
                 (can_tail(labels[v], deg[v]) and can_head(labels[u], deg[u]))
            if ok:
                keep.append((u, v))
            else:
                labels[u] = 'F'
                labels[v] = 'F'
                changed = True
        edges = keep
        if changed:
            continue
    # split F vertices
    fresh = [0]

    def newname():
        fresh[0] += 1
        return ('split', fresh[0])

    new_edges = []
    new_labels = {}
    for (u, v) in edges:
        a, b = u, v
        if labels[u] == 'F':
            a = newname()
            new_labels[a] = 'F'
        else:
            new_labels[u] = labels[u]
        if labels[v] == 'F':
            b = newname()
            new_labels[b] = 'F'
        else:
            new_labels[v] = labels[v]
        new_edges.append((a, b))
    # components
    adj = {}
    for (u, v) in new_edges:
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, []).append(u)
    seen = set()
    comps = []
    for s in adj:
        if s in seen:
            continue
        stack = [s]
        seen.add(s)
        verts = []
        while stack:
            x = stack.pop()
            verts.append(x)
            for y in adj[x]:
                if y not in seen:
                    seen.add(y)
                    stack.append(y)
        vs = set(verts)
        ce = [(u, v) for (u, v) in new_edges if u in vs]
        comps.append(({x: new_labels[x] for x in verts}, ce))
    return comps


def canon(labels, edges):
    """Canonical string of a labelled tree (unordered, unrooted), up to isomorphism.
    Also canonicalises w.r.t. global reversal I<->O (Grundy value is invariant)."""
    adj = {}
    for (u, v) in edges:
        adj.setdefault(u, []).append(v)
        adj.setdefault(v, []).append(u)
    verts = list(adj)
    # find centre(s)
    deg = {x: len(adj[x]) for x in verts}
    leaves = [x for x in verts if deg[x] <= 1]
    remaining = len(verts)
    layer = leaves
    removed = set()
    while remaining > 2:
        nxt = []
        for x in layer:
            removed.add(x)
            remaining -= 1
            for y in adj[x]:
                if y not in removed:
                    deg[y] -= 1
                    if deg[y] == 1:
                        nxt.append(y)
        layer = nxt
    centres = [x for x in verts if x not in removed]

    def enc(lab_map):
        def rec(x, p):
            ch = sorted(rec(y, x) for y in adj[x] if y != p)
            return '(' + lab_map[x] + ''.join(ch) + ')'
        return min(rec(c, None) for c in centres) if len(centres) == 1 else \
            min(rec(centres[0], None), rec(centres[1], None))

    flip = {'N': 'N', 'I': 'O', 'O': 'I', 'F': 'F'}
    s1 = enc(labels)
    s2 = enc({x: flip[l] for x, l in labels.items()})
    return min(s1, s2)


_memo = {}


def comp_grundy(labels, edges):
    key = canon(labels, edges)
    if key in _memo:
        return _memo[key]
    deg = {}
    for u, v in edges:
        deg[u] = deg.get(u, 0) + 1
        deg[v] = deg.get(v, 0) + 1
    opts = set()
    for idx, (u, v) in enumerate(edges):
        for (t, h) in ((u, v), (v, u)):
            if can_tail(labels[t], deg[t]) and can_head(labels[h], deg[h]):
                nl = dict(labels)
                nl[t] = OUT_AFTER[nl[t]]
                nl[h] = IN_AFTER[nl[h]]
                ne = edges[:idx] + edges[idx + 1:]
                # remove isolated vertices implicitly (normalise only uses edge endpoints)
                comps = normalise(nl, ne)
                x = 0
                for (cl, ce) in comps:
                    x ^= comp_grundy(cl, ce)
                opts.add(x)
    g = 0
    while g in opts:
        g += 1
    _memo[key] = g
    return g


def grundy_position(labels, edges):
    x = 0
    for (cl, ce) in normalise(labels, edges):
        x ^= comp_grundy(cl, ce)
    return x


def grundy_original_tree(n, edges):
    labels = {i: 'N' for i in range(n)}
    return grundy_position(labels, edges)


def spider_edges(legs):
    edges = []
    nxt = 1
    for L in legs:
        prev = 0
        for _ in range(L):
            edges.append((prev, nxt))
            prev = nxt
            nxt += 1
    return nxt, edges


if __name__ == "__main__":
    legs = tuple(int(a) for a in sys.argv[1:])
    n, e = spider_edges(legs)
    print(legs, "markable =", sum(legs) - len(legs), "grundy =", grundy_original_tree(n, e))
