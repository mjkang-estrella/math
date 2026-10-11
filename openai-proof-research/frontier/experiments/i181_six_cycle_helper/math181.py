"""Fresh exact graph and linear-algebra primitives, standard library only."""
from fractions import Fraction
from itertools import combinations
from math import gcd
from functools import reduce


def edge(a, b):
    return tuple(sorted((a, b)))


def vector(edges, chosen):
    chosen = set(map(tuple, chosen))
    return tuple(int(e in chosen) for e in edges)


def add(*rows):
    return tuple(map(sum, zip(*rows)))


def scale(a, row):
    return tuple(a*x for x in row)


def sub(a, b):
    return tuple(x-y for x, y in zip(a, b))


def differences(rows):
    return [sub(r, rows[0]) for r in rows[1:]] if rows else []


def primitive(v):
    g = reduce(gcd, v, 0)
    return [x // g for x in v] if g else v


def rank(rows):
    if not rows:
        return 0
    rows = [list(map(Fraction, r)) for r in rows]
    ints = []
    for r in rows:
        den = 1
        for x in r:
            den = den*x.denominator//gcd(den, x.denominator)
        ints.append([int(den*x) for x in r])
    pivots = {}
    for r in ints:
        r = primitive(r)
        for j, b in sorted(pivots.items()):
            if r[j]:
                c, d = r[j], b[j]
                r = primitive([d*x-c*y for x, y in zip(r, b)])
        j = next((i for i, x in enumerate(r) if x), None)
        if j is not None:
            pivots[j] = r
    # Independent column-space elimination, reversed coordinates and row order.
    a = [list(reversed(c)) for c in zip(*reversed(rows))]
    count = 0
    for col in range(len(rows)):
        pivot = next((i for i in range(count, len(a)) if a[i][col]), None)
        if pivot is None:
            continue
        a[count], a[pivot] = a[pivot], a[count]
        d = a[count][col]
        a[count] = [x/d for x in a[count]]
        for i in range(count+1, len(a)):
            if a[i][col]:
                t = a[i][col]
                a[i] = [x-t*y for x, y in zip(a[i], a[count])]
        count += 1
        if count == len(a):
            break
    assert count == len(pivots), (count, len(pivots))
    return count


def basis(rows):
    ans = []
    for r in rows:
        if rank(ans+[r]) > len(ans):
            ans.append(r)
    return ans


def determinant(rows):
    a = [list(map(Fraction, r)) for r in rows]
    ans = Fraction(1)
    for j in range(len(a)):
        i = next((i for i in range(j, len(a)) if a[i][j]), None)
        if i is None:
            return Fraction(0)
        if i != j:
            a[i], a[j] = a[j], a[i]
            ans = -ans
        d = a[j][j]
        ans *= d
        for k in range(j+1, len(a)):
            t = a[k][j]/d
            a[k] = [x-t*y for x, y in zip(a[k], a[j])]
    assert rank(rows) == len(rows)
    return ans


def components(vertices, edges):
    adj = {v: [] for v in vertices}
    for i, (a, b) in enumerate(edges):
        adj[a].append((b, i))
        adj[b].append((a, i))
    seen = set()
    out = []
    for v in sorted(vertices):
        if v in seen:
            continue
        todo, group = [v], set()
        while todo:
            w = todo.pop()
            if w in group:
                continue
            group.add(w)
            todo.extend(x for x, _ in adj[w])
        seen |= group
        out.append(sorted(group))
    return out, adj


def signature(vertices, edges, row):
    chosen = [e for e, bit in zip(edges, row) if bit]
    groups, adj = components(vertices, chosen)
    assert all(len(adj[v]) <= 2 for v in vertices)
    pairs, cycles, singles, words = [], [], [], []
    for group in groups:
        ends = sorted(v for v in group if len(adj[v]) == 1)
        if len(group) == 1 and not adj[group[0]]:
            singles.append(group[0])
            words.append(group)
            continue
        start = ends[0] if ends else min(group)
        word, prev, at = [start], None, start
        while True:
            candidates = [w for w, _ in adj[at] if w != prev]
            if not candidates:
                break
            nxt = min(candidates)
            word.append(nxt)
            if nxt == start:
                break
            prev, at = at, nxt
        if ends:
            assert len(ends) == 2 and len(word) == len(group)
            pairs.append(tuple(ends))
        else:
            assert len(word) == len(group)+1
            cycles.append(word)
        words.append(word)
    return {"pairing": sorted(pairs), "cycles": cycles, "singletons": singles,
            "words": words}


def factors(vertices, edges, target):
    """All binary degree solutions, by branching at a constrained vertex."""
    inc = {v: sum(1 << i for i, e in enumerate(edges) if v in e) for v in vertices}
    full = (1 << len(edges))-1

    def visit(on, off):
        while True:
            changed = False
            choice = None
            for v in vertices:
                rem = inc[v] & ~(on | off)
                have = (inc[v] & on).bit_count()
                need, count = target[v]-have, rem.bit_count()
                if need < 0 or need > count:
                    return
                if count and (need == 0 or need == count):
                    if need:
                        on |= rem
                    else:
                        off |= rem
                    changed = True
                    break
                if count and (choice is None or count < choice[0]):
                    choice = (count, need, rem)
            if not changed:
                break
        if (on | off) == full:
            yield tuple((on >> i) & 1 for i in range(len(edges)))
            return
        _, need, rem = choice
        ids = [i for i in range(len(edges)) if rem >> i & 1]
        for selected in combinations(ids, need):
            mask = sum(1 << i for i in selected)
            yield from visit(on | mask, off | (rem ^ mask))
    return sorted(visit(0, 0))


def path_dfs(vertices, edges, start, finish=None):
    vertices = set(vertices)
    adj = {v: [] for v in vertices}
    for a, b in edges:
        if a in vertices and b in vertices:
            adj[a].append(b)
            adj[b].append(a)
    out = set()

    def walk(word, used):
        v = word[-1]
        if len(used) == len(vertices):
            if finish is None:
                if start not in adj[v]:
                    return
                chosen = [edge(a, b) for a, b in zip(word, word[1:]+[start])]
            else:
                if v != finish:
                    return
                chosen = [edge(a, b) for a, b in zip(word, word[1:])]
            out.add(vector(edges, chosen))
            return
        for w in adj[v]:
            if w not in used and (finish is None or w != finish or len(used)+1 == len(vertices)):
                walk(word+[w], used | {w})
    walk([start], {start})
    return sorted(out)


def packings(vertices, edges, endpoints):
    endpoints = set(endpoints)
    result = {}
    for row in factors(vertices, edges, {v: 1 if v in endpoints else 2 for v in vertices}):
        s = signature(vertices, edges, row)
        if s["cycles"] or s["singletons"]:
            continue
        key = tuple(s["pairing"])
        result.setdefault(key, []).append(row)
    if len(endpoints) == 2:
        a, b = sorted(endpoints)
        assert result.get(((a, b),), []) == path_dfs(vertices, edges, a, b)
    return result


def cycles(vertices, edges):
    rows = [r for r in factors(vertices, edges, {v: 2 for v in vertices})
            if len(components(vertices, [e for e, x in zip(edges, r) if x])[0]) == 1]
    assert rows == path_dfs(vertices, edges, min(vertices))
    return rows


def graph_check(graph, extensions=None):
    edges = sorted(map(tuple, graph["edges"]))
    vertices = sorted({v for e in edges for v in e})
    assert len(edges) == len(set(edges)) and all(a < b for a, b in edges)
    groups, adj = components(vertices, edges)
    assert len(groups) == 1 and all(len(adj[v]) == 3 for v in vertices)
    colors = {vertices[0]: 0}
    todo = [vertices[0]]
    while todo:
        v = todo.pop()
        for w, _ in adj[v]:
            if w not in colors:
                colors[w] = 1-colors[v]
                todo.append(w)
            assert colors[w] != colors[v]
    for a, b in combinations(vertices, 2):
        vs = [v for v in vertices if v not in (a, b)]
        es = [e for e in edges if a not in e and b not in e]
        assert len(components(vs, es)[0]) == 1
    if "faces" in graph:
        darts = []
        links = {v: {} for v in vertices}
        for face in graph["faces"]:
            assert len(face) == len(set(face))
            for j, v in enumerate(face):
                a, b = face[j-1], face[(j+1) % len(face)]
                assert edge(v, b) in edges
                darts.append((v, b))
                assert a not in links[v]
                links[v][a] = b
        assert sorted(darts) == sorted([d for a, b in edges for d in [(a, b), (b, a)]])
        assert len(vertices)-len(edges)+len(graph["faces"]) == 2
        for v, link in links.items():
            at = min(link)
            orbit = []
            while at not in orbit:
                orbit.append(at)
                at = link[at]
            assert len(orbit) == 3 and at == orbit[0]
    if extensions is not None:
        wanted = {tuple(sorted((a, b))) for a, b in combinations(edges, 2) if not set(a)&set(b)}
        got = set()
        for x in extensions:
            if isinstance(x, dict):
                pair = tuple(sorted(x["pair"]))
                matching = {i for i, bit in enumerate(x["matching"]) if bit}
            else:
                pair = tuple(sorted(x[:2]))
                matching = set(x[2])
            pair_edges = tuple(sorted(edges[i] for i in pair))
            matching_edges = {edges[i] for i in matching}
            assert len(matching_edges) == len(matching) == len(vertices)//2
            assert set(pair_edges) <= matching_edges
            assert not set(pair_edges[0]) & set(pair_edges[1])
            assert sorted(v for e in matching_edges for v in e) == vertices
            got.add(pair_edges)
        assert got == wanted
    return {"vertices": len(vertices), "edges": len(edges),
            "matching_extensions": len(extensions) if extensions is not None else None}
