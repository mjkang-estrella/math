"""Fresh exact graph and integer linear-algebra primitives, standard library only."""
from fractions import Fraction
from functools import reduce
from itertools import combinations
from math import gcd


def edge(a, b):
    return (a, b) if a < b else (b, a)


def vector(edges, chosen):
    chosen = {tuple(e) for e in chosen}
    return tuple(int(e in chosen) for e in edges)


def vadd(*rows):
    return tuple(map(sum, zip(*rows)))


def vsub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def vscale(k, row):
    return tuple(k * x for x in row)


def diff_rows(rows):
    return [vsub(r, rows[0]) for r in rows[1:]] if rows else []


def _primitive(row):
    g = reduce(gcd, (abs(x) for x in row), 0)
    return tuple(x // g for x in row) if g else tuple(row)


def rank(rows):
    """Exact rank by two independent methods, cross-checked.

    Method one: primitive integer row elimination over columns.
    Method two: Fraction Gauss elimination on the reversed transpose.
    """
    rows = [tuple(r) for r in rows]
    if not rows:
        return 0
    pivots = {}
    for row in rows:
        cur = _primitive(row)
        for col in sorted(pivots):
            if cur[col]:
                base = pivots[col]
                cur = _primitive(tuple(base[col] * x - cur[col] * y
                                       for x, y in zip(cur, base)))
        nz = [j for j, x in enumerate(cur) if x]
        if nz:
            pivots[nz[0]] = cur
    first = len(pivots)
    grid = [list(reversed(col)) for col in zip(*reversed(rows))]
    second = 0
    for col in range(len(rows)):
        pivot = next((i for i in range(second, len(grid)) if grid[i][col]), None)
        if pivot is None:
            continue
        grid[second], grid[pivot] = grid[pivot], grid[second]
        d = grid[second][col]
        grid[second] = [Fraction(x, d) for x in grid[second]]
        for i in range(second + 1, len(grid)):
            if grid[i][col]:
                t = grid[i][col]
                grid[i] = [x - t * y for x, y in zip(grid[i], grid[second])]
        second += 1
        if second == len(grid):
            break
    assert first == second, (first, second)
    return first


def determinant(rows):
    """Fraction Gauss determinant; asserts nonsingularity via rank()."""
    a = [[Fraction(x) for x in r] for r in rows]
    result = Fraction(1)
    for col in range(len(a)):
        pivot = next((i for i in range(col, len(a)) if a[i][col]), None)
        if pivot is None:
            return Fraction(0)
        if pivot != col:
            a[col], a[pivot] = a[pivot], a[col]
            result = -result
        d = a[col][col]
        result *= d
        for i in range(col + 1, len(a)):
            t = a[i][col] / d
            a[i] = [x - t * y for x, y in zip(a[i], a[col])]
    assert rank(rows) == len(rows)
    return result


def components(vertices, edges):
    """Connected components retaining loops and parallel edges.

    Returns (groups, adjacency) where adjacency lists (neighbor, edge_index)
    pairs; a loop contributes two entries at its vertex.
    """
    adjacency = {v: [] for v in vertices}
    for i, (a, b) in enumerate(edges):
        adjacency[a].append((b, i))
        adjacency[b].append((a, i))
    seen = set()
    groups = []
    for start in sorted(vertices):
        if start in seen:
            continue
        stack, group = [start], set()
        while stack:
            v = stack.pop()
            if v in group:
                continue
            group.add(v)
            stack.extend(w for w, _ in adjacency[v])
        seen |= group
        groups.append(sorted(group))
    return groups, adjacency


def signature(vertices, edges, row):
    """Component structure of a max-degree-2 spanning binary subgraph."""
    chosen = [e for e, bit in zip(edges, row) if bit]
    groups, adjacency = components(vertices, chosen)
    assert all(len(adjacency[v]) <= 2 for v in vertices)
    pairing, cycles, singletons, words = [], [], [], []
    for group in groups:
        ends = sorted(v for v in group if len(adjacency[v]) == 1)
        if len(group) == 1 and not adjacency[group[0]]:
            singletons.append(group[0])
            words.append(group)
            continue
        start = ends[0] if ends else min(group)
        word, prev, at = [start], None, start
        while True:
            candidates = [w for w, _ in adjacency[at] if w != prev]
            if not candidates:
                break
            nxt = min(candidates)
            word.append(nxt)
            if nxt == start:
                break
            prev, at = at, nxt
        if ends:
            assert len(ends) == 2 and len(word) == len(group)
            pairing.append(tuple(ends))
        else:
            assert len(word) == len(group) + 1
            cycles.append(word)
        words.append(word)
    return {"pairing": sorted(pairing), "cycles": cycles,
            "singletons": singletons, "words": words}


def degree_solutions(vertices, edges, target):
    """All binary vectors with the prescribed degree at every vertex."""
    incidence = {v: sum(1 << i for i, e in enumerate(edges) if v in e)
                 for v in vertices}
    full = (1 << len(edges)) - 1

    def search(on, off):
        while True:
            branch = None
            progressed = False
            for v in vertices:
                free = incidence[v] & ~(on | off)
                have = (incidence[v] & on).bit_count()
                need, count = target[v] - have, free.bit_count()
                if need < 0 or need > count:
                    return
                if count and (need == 0 or need == count):
                    if need:
                        on |= free
                    else:
                        off |= free
                    progressed = True
                    break
                if count and (branch is None or count < branch[0]):
                    branch = (count, need, free)
            if not progressed:
                break
        if (on | off) == full:
            yield tuple((on >> i) & 1 for i in range(len(edges)))
            return
        _, need, free = branch
        ids = [i for i in range(len(edges)) if free >> i & 1]
        for picked in combinations(ids, need):
            mask = sum(1 << i for i in picked)
            yield from search(on | mask, off | (free ^ mask))
    return sorted(search(0, 0))


def path_enumeration(vertices, edges, start, finish=None):
    """Independent DFS enumeration of spanning paths/cycles as vectors."""
    vertices = set(vertices)
    adjacency = {v: [] for v in vertices}
    for a, b in edges:
        if a in vertices and b in vertices:
            adjacency[a].append(b)
            adjacency[b].append(a)
    found = set()

    def walk(word, used):
        at = word[-1]
        if len(used) == len(vertices):
            if finish is None:
                if at not in adjacency[start] or at == start:
                    return
                chosen = [edge(u, w) for u, w in zip(word, word[1:] + [start])]
            else:
                if at != finish:
                    return
                chosen = [edge(u, w) for u, w in zip(word, word[1:])]
            found.add(vector(sorted(map(tuple, edges)), chosen))
            return
        for nxt in adjacency[at]:
            if nxt in used:
                continue
            if finish is not None and nxt == finish and len(used) + 1 < len(vertices):
                continue
            walk(word + [nxt], used | {nxt})
    walk([start], {start})
    return sorted(found)


def packings(vertices, edges, endpoints):
    """Spanning degree-2-except-endpoints acyclic subgraphs, by pairing."""
    edges = sorted(map(tuple, edges))
    endpoints = set(endpoints)
    result = {}
    target = {v: 1 if v in endpoints else 2 for v in vertices}
    for row in degree_solutions(vertices, edges, target):
        sig = signature(vertices, edges, row)
        if sig["cycles"] or sig["singletons"]:
            continue
        result.setdefault(tuple(sig["pairing"]), []).append(row)
    if len(endpoints) == 2:
        a, b = sorted(endpoints)
        assert result.get(((a, b),), []) == path_enumeration(vertices, edges, a, b)
    return result


def cycles(vertices, edges):
    """All single-component spanning 2-regular subgraphs, double checked."""
    edges = sorted(map(tuple, edges))
    rows = [r for r in degree_solutions(vertices, edges, {v: 2 for v in vertices})
            if len(components(vertices, [e for e, x in zip(edges, r) if x])[0]) == 1]
    assert rows == path_enumeration(vertices, edges, min(vertices))
    return rows


def graph_check(graph, extensions=None):
    """Cubic simple connected bipartite 2-deletion-connected check plus faces."""
    edges = sorted(map(tuple, graph["edges"]))
    vertices = sorted({v for e in edges for v in e})
    assert len(edges) == len(set(edges)) and all(a < b for a, b in edges)
    groups, adjacency = components(vertices, edges)
    assert len(groups) == 1 and all(len(adjacency[v]) == 3 for v in vertices)
    color = {vertices[0]: 0}
    stack = [vertices[0]]
    while stack:
        v = stack.pop()
        for w, _ in adjacency[v]:
            if w not in color:
                color[w] = 1 - color[v]
                stack.append(w)
            assert color[w] != color[v]
    for a, b in combinations(vertices, 2):
        rest_v = [v for v in vertices if v not in (a, b)]
        rest_e = [e for e in edges if a not in e and b not in e]
        assert len(components(rest_v, rest_e)[0]) == 1
    if "faces" in graph:
        darts = []
        links = {v: {} for v in vertices}
        for face in graph["faces"]:
            assert len(face) == len(set(face))
            for j, v in enumerate(face):
                prev_v, next_v = face[j - 1], face[(j + 1) % len(face)]
                assert edge(v, next_v) in edges
                darts.append((v, next_v))
                assert prev_v not in links[v]
                links[v][prev_v] = next_v
        assert sorted(darts) == sorted(d for a, b in edges
                                       for d in [(a, b), (b, a)])
        assert len(vertices) - len(edges) + len(graph["faces"]) == 2
        for v, link in links.items():
            at, orbit = min(link), []
            while at not in orbit:
                orbit.append(at)
                at = link[at]
            assert len(orbit) == 3 and at == orbit[0]
    if extensions is not None:
        wanted = {tuple(sorted((a, b))) for a, b in combinations(edges, 2)
                  if not set(a) & set(b)}
        got = set()
        for record in extensions:
            if isinstance(record, dict):
                pair = tuple(sorted(record["pair"]))
                matching = {i for i, bit in enumerate(record["matching"]) if bit}
            else:
                pair = tuple(sorted(record[:2]))
                matching = set(record[2])
            pair_edges = tuple(sorted(edges[i] for i in pair))
            matching_edges = {edges[i] for i in matching}
            assert len(matching_edges) == len(matching) == len(vertices) // 2
            assert set(pair_edges) <= matching_edges
            assert not set(pair_edges[0]) & set(pair_edges[1])
            assert sorted(v for e in matching_edges for v in e) == vertices
            got.add(pair_edges)
        assert got == wanted
    return {"vertices": len(vertices), "edges": len(edges),
            "matching_extensions": len(extensions) if extensions is not None else None}
