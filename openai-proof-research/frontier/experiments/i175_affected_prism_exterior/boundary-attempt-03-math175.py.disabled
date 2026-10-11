"""Independently written finite graph and exact rational certificate routines."""
from fractions import Fraction
from functools import lru_cache
from itertools import combinations
from math import gcd


def edge(a, b):
    return tuple(sorted((a, b)))


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def add(*vs):
    return tuple(map(sum, zip(*vs)))


def diff(vs):
    return [sub(v, vs[0]) for v in vs[1:]] if vs else []


def integer_basis(rows):
    pivots = {}
    chosen = []
    for original in rows:
        v = list(original)
        for p, w in sorted(pivots.items()):
            if v[p]:
                a, b = w[p], v[p]
                v = [a*x-b*y for x, y in zip(v, w)]
                g = 0
                for x in v:
                    g = gcd(g, x)
                if g > 1:
                    v = [x//g for x in v]
        if any(v):
            p = next(i for i, x in enumerate(v) if x)
            g = 0
            for x in v:
                g = gcd(g, x)
            if v[p] < 0:
                g = -g
            pivots[p] = tuple(x//g for x in v)
            chosen.append(tuple(original))
    return chosen


def fraction_rank(rows):
    pivots = {}
    for row in reversed(rows):
        r = {j: Fraction(x) for j, x in enumerate(row) if x}
        while r:
            j = max(r)
            a = r[j]
            if j not in pivots:
                pivots[j] = {k: v/a for k, v in r.items()}
                break
            for k, v in pivots[j].items():
                t = r.get(k, 0)-a*v
                if t:
                    r[k] = t
                else:
                    r.pop(k, None)
    return len(pivots)


@lru_cache(maxsize=2048)
def ranks(rows):
    a = len(integer_basis(rows))
    b = fraction_rank(rows)
    assert a == b, (a, b)
    return a


def rank(rows):
    return ranks(tuple(tuple(r) for r in rows))


def adjacency(edges):
    d = {}
    for a, b in edges:
        d.setdefault(a, []).append(b)
        d.setdefault(b, []).append(a)
    return {v: sorted(ns) for v, ns in d.items()}


def components(edges, vertices):
    a = {v: [] for v in vertices}
    for u, v in edges:
        a[u].append(v)
        a[v].append(u)
    left = set(vertices)
    parts = []
    while left:
        todo = [min(left)]
        part = set(todo)
        left.remove(todo[0])
        for v in todo:
            for w in a[v]:
                if w in left:
                    left.remove(w)
                    part.add(w)
                    todo.append(w)
        parts.append(sorted(part))
    return sorted(parts)


def canonical(f):
    return min(tuple(f[i:]+f[:i]) for i in range(len(f)))


def normalize(edges, faces):
    return {"n": len(adjacency(edges)), "edges": sorted(set(edge(*e) for e in edges)),
            "faces": sorted(canonical(list(f)) for f in faces)}


def rotation(graph):
    r = {v: {} for v in adjacency(graph["edges"])}
    for f in graph["faces"]:
        for i, v in enumerate(f):
            u, w = f[i-1], f[(i+1) % len(f)]
            assert u not in r[v]
            r[v][u] = w
    return r


def faces_from_rotation(r):
    unseen = {(u, v) for u in r for v in r[u]}
    fs = []
    while unseen:
        start = min(unseen)
        dart = start
        face = []
        while True:
            assert dart in unseen
            unseen.remove(dart)
            u, v = dart
            face.append(u)
            dart = (v, r[v][u])
            if dart == start:
                break
        fs.append(face)
    return fs


def certify(g, sphere=True):
    es = [tuple(e) for e in g["edges"]]
    a = adjacency(es)
    assert len(es) == len(set(es)) and all(u < v for u, v in es)
    assert all(len(ns) == 3 for ns in a.values())
    color = {min(a): 0}
    todo = [min(a)]
    for v in todo:
        for w in a[v]:
            if w not in color:
                color[w] = 1-color[v]
                todo.append(w)
            assert color[w] != color[v]
    assert len(color) == len(a)
    for removed in combinations(a, 2):
        rest = set(a)-set(removed)
        assert len(components([e for e in es if not set(e) & set(removed)], rest)) == 1
    r = rotation(g)
    assert set((u, v) for u in r for v in r[u]) == {(u, v) for e in es for u, v in (e, e[::-1])}
    for v, rs in r.items():
        s = min(rs)
        assert rs[rs[rs[s]]] == s and len({s, rs[s], rs[rs[s]]}) == 3
    chi = len(a)-len(es)+len(g["faces"])
    if sphere:
        assert chi == 2
    return {"n": len(a), "edges": len(es), "euler": chi, "three_connected": True,
            "bipartition": [[v for v in sorted(a) if color[v] == c] for c in (0, 1)]}


def prism(k):
    es = [(i, (i+1) % k) for i in range(k)]
    es += [(k+i, k+(i+1) % k) for i in range(k)]
    es += [(i, k+i) for i in range(k)]
    fs = [list(range(k)), list(reversed(range(k, 2*k)))]
    fs += [[(i+1) % k, i, k+i, k+(i+1) % k] for i in range(k)]
    return normalize(es, fs)


def splice(h, z, a, hole, portmap, offset, reverse=False):
    rh, ra = rotation(h), rotation(a)
    if reverse:
        ra = {v: {w: u for u, w in rs.items()} for v, rs in ra.items()}
    assert set(portmap) == set(rh[z]) and set(portmap.values()) == set(ra[hole])
    r = {}
    for v, rs in rh.items():
        if v == z:
            continue
        change = lambda w: portmap[v]+offset if w == z else w
        r[v] = {change(u): change(w) for u, w in rs.items()}
    inv = {w: v for v, w in portmap.items()}
    for v, rs in ra.items():
        if v == hole:
            continue
        change = lambda w: inv[v] if w == hole else w+offset
        r[v+offset] = {change(u): change(w) for u, w in rs.items()}
    return normalize([edge(v, w) for v in r for w in r[v]], faces_from_rotation(r))


def square(g, triple):
    face_no, i, j = triple
    f = list(g["faces"][face_no])
    u, v, y, x = f[i], f[(i+1) % len(f)], f[j], f[(j+1) % len(f)]
    assert len({u, v, x, y}) == 4
    es = set(map(tuple, g["edges"]))
    p = max(adjacency(es))+1
    q, r, s = p+1, p+2, p+3
    es -= {edge(u, v), edge(x, y)}
    es |= {edge(*e) for e in [(u, p), (v, q), (x, r), (y, s),
                              (p, q), (q, s), (s, r), (r, p)]}
    fs = []
    target = None
    for no, old in enumerate(g["faces"]):
        out = []
        for t, b in enumerate(old):
            c = old[(t+1) % len(old)]
            out.append(b)
            if edge(b, c) == edge(u, v):
                out += [p, q] if b == u else [q, p]
            if edge(b, c) == edge(x, y):
                out += [r, s] if b == x else [s, r]
        if no == face_no:
            target = out
        else:
            fs.append(out)
    # Three faces replacing the expanded old face.
    def segment(start, end):
        k = target.index(start)
        out = [start]
        while out[-1] != end:
            k = (k+1) % len(target)
            out.append(target[k])
        return out
    fs += [segment(q, s), segment(r, p), [p, q, s, r]]
    return normalize(es, fs)


def matchings(es, forced=()):
    a = adjacency(es)
    used = set()
    picked = []
    for idx in forced:
        u, v = es[idx]
        if u in used or v in used:
            return
        used.update((u, v))
        picked.append(idx)
    incident = {v: [] for v in a}
    for i, (u, v) in enumerate(es):
        incident[u].append((v, i))
        incident[v].append((u, i))

    def go(left, selected):
        if not left:
            yield tuple(sorted(selected))
            return
        v = min(left, key=lambda w: (sum(u in left for u, _ in incident[w]), w))
        for u, i in incident[v]:
            if u in left:
                yield from go(left-{u, v}, selected+[i])
    yield from go(set(a)-used, picked)


def vector(es, selected):
    s = set(selected)
    return tuple(int(i in s) for i in range(len(es)))


def selected_edges(es, v):
    return [e for e, x in zip(es, v) if x]


def cycle_sets(es):
    vertices = set(adjacency(es))
    out = []
    for m in matchings(es):
        v = tuple(1-x for x in vector(es, m))
        if len(components(selected_edges(es, v), vertices)) == 1:
            out.append(v)
    return sorted(out)


def path_dfs(es, start, end=None):
    a = adjacency(es)
    ix = {tuple(e): i for i, e in enumerate(es)}
    out = set()

    def go(v, visited, chosen):
        if len(visited) == len(a):
            if end is None and start in a[v]:
                out.add(vector(es, chosen+[ix[edge(v, start)]]))
            elif v == end:
                out.add(vector(es, chosen))
            return
        for w in a[v]:
            if w not in visited and (w != end or len(visited) == len(a)-1):
                go(w, visited | {w}, chosen+[ix[edge(v, w)]])
    go(start, {start}, [])
    return sorted(out)


def degree_subgraphs(es, target, forbidden):
    """Assign all edges incident to a least-choice unprocessed vertex."""
    incident = {v: [] for v in target}
    for i, (u, v) in enumerate(es):
        if i not in forbidden:
            incident[u].append(i)
            incident[v].append(i)
    output = []

    def go(need, free, chosen):
        if not free:
            if not any(need.values()):
                output.append(vector(es, chosen))
            return
        choices = []
        for v in need:
            avail = [i for i in incident[v] if i in free]
            if need[v] < 0 or need[v] > len(avail):
                return
            if avail:
                choices.append((min(need[v], len(avail)-need[v]), len(avail), v, avail))
            elif need[v]:
                return
        if not choices:
            return
        _, _, v, avail = min(choices)
        for take in combinations(avail, need[v]):
            nn = dict(need)
            for idx in take:
                for w in es[idx]:
                    nn[w] -= 1
            go(nn, free-set(avail), chosen+list(take))
    go(dict(target), set(range(len(es)))-set(forbidden), [])
    return sorted(output)


def seven(g, uvxy, dfs_check=False):
    es = list(map(tuple, g["edges"]))
    vs = set(adjacency(es))
    u, v, x, y = uvxy
    ei, fi = es.index(edge(u, v)), es.index(edge(x, y))
    cs = cycle_sets(es)
    if dfs_check:
        assert cs == path_dfs(es, min(vs))
    fam = {key: [] for key in ["N00", "N10", "N01", "N11", "Pux", "Pvy", "D11"]}
    for c in cs:
        fam["N%d%d" % (c[ei], c[fi])].append(c)
    for key, endpoints in [("Pux", (u, x)), ("Pvy", (v, y)), ("D11", (u, v, x, y))]:
        target = {w: 1 if w in endpoints else 2 for w in vs}
        for c in degree_subgraphs(es, target, {ei, fi}):
            parts = components(selected_edges(es, c), vs)
            if len(endpoints) == 2:
                valid = len(parts) == 1
            else:
                valid = len(parts) == 2 and any(u in p and v in p for p in parts) and any(x in p and y in p for p in parts)
            if valid:
                fam[key].append(c)
        if dfs_check and len(endpoints) == 2:
            pe = [e for i, e in enumerate(es) if i not in (ei, fi)]
            mapped = []
            for c in path_dfs(pe, endpoints[0], endpoints[1]):
                se = set(selected_edges(pe, c))
                mapped.append(tuple(int(e in se) for e in es))
            assert sorted(mapped) == fam[key]
    return cs, fam


def interface(g, uvxy):
    u, v, x, y = uvxy
    for face in g["faces"]:
        for orient in (list(face), list(reversed(face))):
            if u not in orient:
                continue
            i = orient.index(u)
            f = orient[i:]+orient[:i]
            if f[1] == v and y in f and f[(f.index(y)+1) % len(f)] == x:
                return f
    raise AssertionError(("interface not facial", uvxy))


def analyse(g, uvxy, dfs_check=False):
    cert = certify(g)
    es = list(map(tuple, g["edges"]))
    cs, f = seven(g, uvxy, dfs_check)
    assert all(f.values()), "seven families required by this diagnostic"
    u, v, x, y = uvxy
    face = interface(g, uvxy)
    cut = face.index(y)
    arcs = [list(reversed(face[cut+1:]+[u])), face[1:cut+1]]
    qs = []
    for arc in arcs:
        q = [0]*len(es)
        for j in range(len(arc)-1):
            q[es.index(edge(arc[j], arc[j+1]))] = (-1)**j
        qs.append(tuple(q))
    assert all((len(a)-1) % 2 for a in arcs)
    survivor = sorted(f["N10"]+f["N01"]+f["N11"])
    L, V = diff(survivor), diff(f["N00"])
    L0 = sum((diff(f[k]) for k in ("N10", "N01", "N11")), [])
    U = sum((diff(f[k]) for k in ("Pux", "Pvy", "D11")), [])
    good, residual, records = [], [], {}
    for key, q in zip(("Pux", "Pvy", "D11"), qs+[add(*qs)]):
        good_old = [n for n in f["N00"] if sub(n, q) in f[key]]
        translated = [sub(n, q) for n in good_old]
        anchor = translated[0] if translated else f[key][0]
        rest = [n for n in f[key] if n not in translated]
        dirs = [sub(n, anchor) for n in rest]
        good += diff(good_old)
        residual += dirs
        records[key] = {"q": q, "good": good_old, "anchor": anchor,
                        "residual": rest, "residual_directions": dirs}
    assert rank(U) == rank(good+residual) == rank(U+good+residual)
    C0 = survivor[0]
    A, B, C, N = (f[k][0] for k in ("N10", "N01", "N11", "N00"))
    w = [0]*len(es)
    w[es.index(edge(u, v))] = w[es.index(edge(x, y))] = 2
    base = add(f["Pux"][0], f["Pvy"][0], f["D11"][0], w)
    b = sub(base, tuple(3*t for t in C0))
    beta = sub(base, add(A, B, C))
    c = add(N, tuple(-t for t in A), tuple(-t for t in B), C)
    rL, r0 = rank(L), rank(L0)
    LU = rank(L+U)
    eta = rank(L+U+[b])-LU
    assert rank(L+U+[beta])-LU == eta and rank(L+U+[sub(b, beta)]) == LU
    deltaV = rank(L0+V)-rank(L0+good)
    deltaR = rank(L0+good+residual)-rank(L0+good)
    epsilon = rank(L0+V+[c])-rank(L0+V)
    dg = rank(diff(cs))
    ell, t = dg-rL, LU-rL
    assert ell-t == deltaV+epsilon-deltaR
    ei, fi = es.index(edge(u, v)), es.index(edge(x, y))
    assert rank([(a[ei], a[fi]) for a in L]) == 2
    row = {"n": cert["n"], "dg": dg, "rankL": rL, "rankL0": r0,
           "rankU": rank(U), "rankUV": rank(U+V),
           "ell": ell, "t": t, "eta": eta, "delta_V": deltaV,
           "delta_R": deltaR, "epsilon": epsilon,
           "arcs": [len(a)-1 for a in arcs], "counts": {k: len(v) for k, v in f.items()}}
    return {"graph": g, "uvxy": uvxy, "certification": cert, "cycles": cs, "families": f,
            "row": row, "bridge": b, "beta": beta, "c": c, "residuals": records,
            "survivor_basis": integer_basis(L), "survivor_anchor": C0}


def brace(g):
    es = list(map(tuple, g["edges"]))
    successes, failures = [], []
    for i, j in combinations(range(len(es)), 2):
        if set(es[i]) & set(es[j]):
            continue
        m = next(matchings(es, (i, j)), None)
        if m is None:
            failures.append([i, j])
        else:
            assert len(m)*2 == g["n"] and {v for k in m for v in es[k]} == set(adjacency(es))
            successes.append([i, j, m])
    return {"brace": not failures, "extensions": successes, "failures": failures}


def port_groups(g, cycles, vertex):
    es = list(map(tuple, g["edges"]))
    ix = [i for i, e in enumerate(es) if vertex in e]
    groups = {}
    for c in cycles:
        sig = tuple(c[i] for i in ix)
        groups.setdefault(sig, []).append(c)
    return ix, {s: sorted(v) for s, v in sorted(groups.items())}
