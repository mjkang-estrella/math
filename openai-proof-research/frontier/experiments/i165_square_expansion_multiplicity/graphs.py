"""I165 independent, standard-library embedded cubic graph diagnostics."""
from collections import Counter
from itertools import combinations


def edge(a, b):
    return tuple(sorted((a, b)))


def edges(faces):
    return sorted({edge(a, b) for f in faces for a, b in zip(f, f[1:] + f[:1])})


def adjacency(es):
    out = {}
    for a, b in es:
        out.setdefault(a, set()).add(b)
        out.setdefault(b, set()).add(a)
    return {v: sorted(ns) for v, ns in sorted(out.items())}


def orient(faces):
    faces = [list(f) for f in faces]
    incidences = {}
    for i, f in enumerate(faces):
        for a, b in zip(f, f[1:] + f[:1]):
            incidences.setdefault(edge(a, b), []).append((i, a < b))
    assert all(len(x) == 2 for x in incidences.values())
    links = {i: [] for i in range(len(faces))}
    for ((i, d), (j, e)) in incidences.values():
        links[i].append((j, d == e))
        links[j].append((i, d == e))
    flips = {0: False}
    stack = [0]
    while stack:
        i = stack.pop()
        for j, toggle in links[i]:
            want = flips[i] ^ toggle
            if j in flips:
                assert flips[j] == want
            else:
                flips[j] = want
                stack.append(j)
    assert len(flips) == len(faces)
    return [f[::-1] if flips[i] else f for i, f in enumerate(faces)]


def prism(m):
    assert m >= 4 and m % 2 == 0
    return orient([list(range(m)), list(range(m, 2*m))] +
                  [[i, (i+1) % m, m+(i+1) % m, m+i] for i in range(m)])


def connected(adj, removed=()):
    left = set(adj) - set(removed)
    if not left:
        return True
    stack = [min(left)]
    left.remove(stack[0])
    while stack:
        for w in adj[stack.pop()]:
            if w in left:
                left.remove(w)
                stack.append(w)
    return not left


def certificate(faces):
    es = edges(faces)
    adj = adjacency(es)
    assert all(len(ns) == 3 for ns in adj.values())
    assert all(len(f) == len(set(f)) and len(f) >= 4 for f in faces)
    # A consistent oriented closed surface with a single link at each vertex.
    darts = Counter((a, b) for f in faces for a, b in zip(f, f[1:] + f[:1]))
    assert set(darts) == {(a, b) for a, b in es} | {(b, a) for a, b in es}
    assert all(c == 1 for c in darts.values())
    rotations = {}
    for v in adj:
        succ = {}
        for f in faces:
            if v in f:
                j = f.index(v)
                succ[f[j-1]] = f[(j+1) % len(f)]
        a = adj[v][0]
        assert set(succ) == set(adj[v])
        assert succ[succ[succ[a]]] == a and succ[a] != a
        rotations[v] = [a, succ[a], succ[succ[a]]]
    assert len(adj) - len(es) + len(faces) == 2
    color = {}
    for v in adj:
        if v not in color:
            color[v] = 0
            stack = [v]
            while stack:
                a = stack.pop()
                for b in adj[a]:
                    if b not in color:
                        color[b] = 1-color[a]
                        stack.append(b)
                    assert color[b] != color[a]
    tested = 0
    for k in range(3):
        for cut in combinations(adj, k):
            assert connected(adj, cut), cut
            tested += 1
    return {"n": len(adj), "edges": [list(e) for e in es],
            "faces": faces, "rotation": {str(v): x for v, x in rotations.items()},
            "bipartition": [[v for v in adj if color[v] == c] for c in (0, 1)],
            "euler_characteristic": 2, "vertex_deletions_checked": tested}


def steps(faces):
    for fi, f in enumerate(faces):
        # Each unordered pair of face edges once; residual lengths are odd.
        for i in range(len(f)):
            for j in range(i+2, len(f)):
                if (j-i) % 2 == 0:
                    yield (fi, i, j)


def square(faces, step):
    fi, i, j = step
    f = faces[fi]
    assert j-i >= 2 and (j-i) % 2 == 0 and j < len(f)
    u, v, y, x = f[i], f[(i+1) % len(f)], f[j], f[(j+1) % len(f)]
    assert len({u, v, x, y}) == 4
    p = 1 + max(adjacency(edges(faces)))
    q, r, s = p+1, p+2, p+3
    replacements = {(u, v): [u, p, q], (v, u): [v, q, p],
                    (x, y): [x, r, s], (y, x): [y, s, r]}
    out = []
    for k, face in enumerate(faces):
        if k != fi:
            row = []
            for a, b in zip(face, face[1:] + face[:1]):
                row.extend(replacements.get((a, b), [a]))
            out.append(row)
    out += [f[i+1:j+1] + [s, q], f[j+1:] + f[:i+1] + [p, r],
            [p, q, s, r]]
    return orient(out), (u, v, x, y)


def cube_expand(faces, v):
    adj = adjacency(edges(faces))
    ns = adj[v]
    start = max(adj) + 1
    bits = {b: start+b-1 for b in range(1, 8)}
    ports = dict(zip(ns, (1, 2, 4)))
    out = []
    for f in faces:
        row = []
        for i, w in enumerate(f):
            if w != v:
                row.append(w)
            else:
                a, b = ports[f[i-1]], ports[f[(i+1) % len(f)]]
                row.extend([bits[a], bits[a+b], bits[b]])
        out.append(row)
    out += [[bits[x] for x in f] for f in
            ([1, 3, 7, 5], [2, 3, 7, 6], [4, 5, 7, 6])]
    return orient(out)


def splice(faces, v, other, w, port_map):
    """Remove v,w; port_map maps each neighbor of v to a neighbor of w."""
    a, b = adjacency(edges(faces)), adjacency(edges(other))
    assert set(port_map) == set(a[v])
    assert set(port_map.values()) == set(b[w])
    start = max(a)+1
    relabel = {x: start+i for i, x in enumerate(sorted(b))}
    out = [f[:] for f in faces if v not in f]
    out += [[relabel[x] for x in f] for f in other if w not in f]
    for f in faces:
        if v not in f:
            continue
        j = f.index(v)
        arc = f[j+1:] + f[:j]
        aa, bb = port_map[arc[-1]], port_map[arc[0]]
        candidates = []
        for of in other:
            if w in of:
                k = of.index(w)
                oa = of[k+1:] + of[:k]
                if {oa[0], oa[-1]} == {aa, bb}:
                    candidates.append(oa if oa[0] == aa else oa[::-1])
        assert len(candidates) == 1
        out.append(arc + [relabel[x] for x in candidates[0]])
    return orient(out), relabel


def matching_factors(es):
    """Enumerate perfect matchings, retaining complement and components."""
    adj = adjacency(es)
    vs = sorted(adj)
    bit = {v: 1 << i for i, v in enumerate(vs)}
    all_edges = frozenset(es)
    ans = []
    def rec(left, matching):
        if not left:
            fac = all_edges - frozenset(matching)
            fa = adjacency(fac)
            unseen = set(vs)
            comps = []
            while unseen:
                seen = {min(unseen)}
                stack = list(seen)
                while stack:
                    for b in fa[stack.pop()]:
                        if b not in seen:
                            seen.add(b)
                            stack.append(b)
                unseen -= seen
                comps.append(frozenset(seen))
            ans.append((fac, comps))
            return
        candidates = [(sum(bool(left & bit[w]) for w in adj[v]), v)
                      for v in vs if left & bit[v]]
        _, a = min(candidates)
        for b in adj[a]:
            if left & bit[b]:
                rec(left ^ bit[a] ^ bit[b], matching + [edge(a, b)])
    rec((1 << len(vs))-1, [])
    return ans


def dfs_cycles(es):
    """Independent anchored vertex-path enumeration; no matching code."""
    adj = adjacency(es)
    root = min(adj)
    target = len(adj)
    ans = set()
    def rec(path, used):
        a = path[-1]
        if len(path) == target:
            if root in adj[a] and path[1] < a:
                ans.add(frozenset(edge(x, y) for x, y in
                                  zip(path, path[1:] + [root])))
            return
        for b in adj[a]:
            if b not in used:
                rec(path+[b], used | {b})
    rec([root], {root})
    return ans


def dfs_paths(es, a, b):
    adj = adjacency(es)
    target = len(adj)
    ans = set()
    def rec(path, used):
        v = path[-1]
        if v == b:
            if len(path) == target:
                ans.add(frozenset(edge(x, y) for x, y in zip(path, path[1:])))
            return
        for w in adj[v]:
            if w not in used:
                rec(path+[w], used | {w})
    rec([a], {a})
    return ans


def pruned_paths(es, source, target=None):
    """Vertex DFS with necessary residual degree/connectivity pruning."""
    adj = adjacency(es)
    vertices = sorted(adj)
    bit = {v: 1 << i for i, v in enumerate(vertices)}
    masks = {v: sum(bit[w] for w in adj[v]) for v in vertices}
    all_mask = (1 << len(vertices))-1
    cycles = target is None
    if cycles:
        target = source
    result = set()
    def rec(path, left):
        tip = path[-1]
        if not left:
            if cycles:
                if source in adj[tip] and path[1] < tip:
                    result.add(frozenset(edge(a, b) for a, b in
                                        zip(path, path[1:]+[source])))
            elif tip == target:
                result.add(frozenset(edge(a, b) for a, b in zip(path, path[1:])))
            return
        if not cycles and tip == target:
            return
        allowed = left | bit[tip] | (bit[source] if cycles else 0)
        # Every unused vertex needs two residual incident edges except the target.
        for v in vertices:
            if left & bit[v]:
                needed = 1 if not cycles and v == target else 2
                if (masks[v] & allowed).bit_count() < needed:
                    return
        if not masks[tip] & left:
            return
        if cycles and not masks[source] & (left | bit[tip]):
            return
        reached = bit[tip]
        frontier = reached
        while frontier:
            nxt = 0
            for v in vertices:
                if frontier & bit[v]:
                    nxt |= masks[v]
            nxt &= allowed & ~reached
            reached |= nxt
            frontier = nxt
        if reached != allowed:
            return
        for w in adj[tip]:
            if left & bit[w]:
                rec(path+[w], left ^ bit[w])
    rec([source], all_mask ^ bit[source])
    return result


def boundary(faces, step, independent=False):
    es = edges(faces)
    new, (u, v, x, y) = square(faces, step)
    e, f = edge(u, v), edge(x, y)
    fs = matching_factors(es)
    hs = {fac for fac, comp in fs if len(comp) == 1}
    nhs = {fac for fac, comp in matching_factors(edges(new)) if len(comp) == 1}
    n00 = {h for h in hs if e not in h and f not in h}
    d11 = {fac for fac, comp in fs if len(comp) == 2 and e in fac and f in fac
           and not any(u in c and x in c for c in comp)}
    k = [z for z in es if z not in (e, f)]
    pux, pvy = pruned_paths(k, u, x), pruned_paths(k, v, y)
    assert len(nhs) == len(hs)-len(n00)+len(d11)+len(pux)+len(pvy)
    assert min(len(d11), len(pux), len(pvy)) >= 1
    if independent:
        check_old, check_new = (independent if isinstance(independent, tuple) else
                                (dfs_cycles(es), dfs_cycles(edges(new))))
        assert check_old == hs
        assert check_new == nhs
    return {"h": len(hs), "h_prime": len(nhs), "N00": len(n00),
            "Pux": len(pux), "Pvy": len(pvy), "D11": len(d11),
            "gain": len(nhs)-len(hs), "terminals": [u, v, x, y]}


def arm_fibres(faces, step, new_cycles):
    """Check E's six classes as exact sets, including all inverse fibres."""
    es = edges(faces)
    new, (u, v, x, y) = square(faces, step)
    p = max(adjacency(es))+1
    q, r, s = p+1, p+2, p+3
    arms = {edge(u, p): u, edge(v, q): v, edge(x, r): x, edge(y, s): y}
    e, f = edge(u, v), edge(x, y)
    k = set(es)-{e, f}
    fs = matching_factors(es)
    hs = {h for h, c in fs if len(c) == 1}
    expected = {
        "N10": {h for h in hs if e in h and f not in h},
        "N01": {h for h in hs if f in h and e not in h},
        "N11": {h for h in hs if e in h and f in h},
        "Pux": pruned_paths(sorted(k), u, x),
        "Pvy": pruned_paths(sorted(k), v, y),
        "D11": {h for h, c in fs if len(c) == 2 and e in h and f in h
                and not any(u in cc and x in cc for cc in c)}
    }
    actual = {name: [] for name in expected}
    for h in new_cycles:
        ports = frozenset(arms[z] for z in h if z in arms)
        exterior = h & k
        if len(ports) == 2:
            table = {frozenset((u, v)): ("N10", exterior | {e}),
                     frozenset((x, y)): ("N01", exterior | {f}),
                     frozenset((u, x)): ("Pux", exterior),
                     frozenset((v, y)): ("Pvy", exterior)}
            assert ports in table
            name, witness = table[ports]
        else:
            assert len(ports) == 4
            witness = exterior | {e, f}
            name = "N11" if connected(adjacency(witness)) else "D11"
        actual[name].append(frozenset(witness))
    for name in actual:
        assert len(actual[name]) == len(set(actual[name]))
        assert set(actual[name]) == expected[name]
    return {name: len(actual[name]) for name in actual}
