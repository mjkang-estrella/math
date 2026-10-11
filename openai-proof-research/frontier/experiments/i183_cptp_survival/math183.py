"""Fresh exact graph and rational linear-algebra primitives for I183.

Standard library only.  Every rank is computed by two independent exact
methods and the results are asserted equal at every call:

  * method A: fraction-free integer Gaussian elimination with gcd
    pivot normalization, processing rows in the given order;
  * method B: exact Fraction elimination on the transpose processed in
    reversed column order.

Determinants use the Bareiss fraction-free algorithm and are certified
nonsingular by an independent rank computation.
"""
from fractions import Fraction
from itertools import combinations
from math import gcd


def edge(a, b):
    return (a, b) if a <= b else (b, a)


def vector(edges, chosen):
    wanted = {tuple(e) for e in chosen}
    return tuple(1 if e in wanted else 0 for e in edges)


def vadd(*rows):
    return tuple(sum(coords) for coords in zip(*rows))


def vsub(a, b):
    return tuple(x - y for x, y in zip(a, b))


def vscale(k, row):
    return tuple(k * x for x in row)


def diff_rows(rows):
    return [vsub(r, rows[0]) for r in rows[1:]] if rows else []


def _rank_integer(rows):
    """Fraction-free elimination: maintain diagonal pivots exactly."""
    mat = [list(r) for r in rows if any(r)]
    if not mat:
        return 0
    width = len(mat[0])
    rank = 0
    for col in range(width):
        pivot = None
        for i in range(rank, len(mat)):
            if mat[i][col]:
                pivot = i
                break
        if pivot is None:
            continue
        mat[rank], mat[pivot] = mat[pivot], mat[rank]
        for i in range(rank + 1, len(mat)):
            if mat[i][col]:
                a, b = mat[rank][col], mat[i][col]
                g = gcd(abs(a), abs(b))
                ra, rb = b // g, a // g
                mat[i] = [ra * x - rb * y for x, y in zip(mat[i], mat[rank])]
        rank += 1
        if rank == len(mat):
            break
    return rank


def _rank_fraction_transposed(rows):
    """Fraction Gauss elimination on the reversed transpose."""
    grid = [list(col) for col in zip(*rows)]
    grid.reverse()
    grid = [list(reversed(col)) for col in zip(*grid)]
    if not grid:
        return 0
    height, width = len(grid), len(grid[0])
    rank = 0
    for col in range(width):
        pivot = None
        for i in range(rank, height):
            if grid[i][col]:
                pivot = i
                break
        if pivot is None:
            continue
        grid[rank], grid[pivot] = grid[pivot], grid[rank]
        inv = Fraction(1, grid[rank][col])
        grid[rank] = [x * inv for x in grid[rank]]
        for i in range(height):
            if i != rank and grid[i][col]:
                factor = grid[i][col]
                grid[i] = [x - factor * y
                           for x, y in zip(grid[i], grid[rank])]
        rank += 1
        if rank == height:
            break
    return rank


def rank(rows):
    rows = [tuple(r) for r in rows]
    if not rows:
        return 0
    first = _rank_integer(rows)
    second = _rank_fraction_transposed(rows)
    assert first == second, (first, second)
    return first


def determinant(rows):
    """Bareiss fraction-free determinant with exactness assertions."""
    mat = [list(r) for r in rows]
    n = len(mat)
    assert all(len(r) == n for r in mat)
    sign = 1
    prev = 1
    for col in range(n - 1):
        pivot = None
        for i in range(col, n):
            if mat[i][col]:
                pivot = i
                break
        if pivot is None:
            assert rank(rows) < n
            return Fraction(0)
        if pivot != col:
            mat[col], mat[pivot] = mat[pivot], mat[col]
            sign = -sign
        for i in range(col + 1, n):
            for j in range(col + 1, n):
                num = mat[i][j] * mat[col][col] - mat[i][col] * mat[col][j]
                assert num % prev == 0
                mat[i][j] = num // prev
            mat[i][col] = 0
        prev = mat[col][col]
    result = Fraction(sign * mat[n - 1][n - 1]) if n else Fraction(1)
    if result:
        assert rank(rows) == n
    else:
        assert rank(rows) < n
    return result


def components(vertices, edges):
    """Union-find components; loops and parallel edges are retained in
    the returned adjacency (a loop contributes two entries)."""
    parent = {v: v for v in vertices}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    adjacency = {v: [] for v in vertices}
    for i, (a, b) in enumerate(edges):
        adjacency[a].append((b, i))
        adjacency[b].append((a, i))
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    groups = {}
    for v in vertices:
        groups.setdefault(find(v), []).append(v)
    return sorted(map(sorted, groups.values())), adjacency


def signature(vertices, edges, bits):
    """Decompose a spanning max-degree-2 binary subgraph.

    Returns pairing (degree-1 endpoint pairs), cycles (closed words),
    singletons and raw component words.  Loops and parallel two-edge
    components are treated as cycles, never contracted away.
    """
    chosen = [e for e, bit in zip(edges, bits) if bit]
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
            options = [w for w, _ in adjacency[at] if w != prev]
            if not options:
                break
            nxt = min(options)
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
    """All 0/1 edge vectors with prescribed degrees, by constraint
    propagation with least-branching recursion."""
    incidence = {v: [] for v in vertices}
    for i, e in enumerate(edges):
        for v in e:
            incidence[v].append(i)
    order = sorted(vertices, key=lambda v: len(incidence[v]))
    solutions = []

    def recurse(chosen, banned):
        changed = True
        while changed:
            changed = False
            for v in order:
                have = sum(1 for i in incidence[v] if i in chosen)
                free = [i for i in incidence[v]
                        if i not in chosen and i not in banned]
                need = target[v] - have
                if need < 0 or need > len(free):
                    return
                if need == 0 and free:
                    banned |= set(free)
                    changed = True
                elif need == len(free) and free:
                    chosen |= set(free)
                    changed = True
        if len(chosen) + len(banned) == len(edges):
            solutions.append(tuple(1 if i in chosen else 0
                                   for i in range(len(edges))))
            return
        best, best_free = None, None
        for v in order:
            free = [i for i in incidence[v]
                    if i not in chosen and i not in banned]
            need = target[v] - sum(1 for i in incidence[v] if i in chosen)
            if free and (best is None or len(free) < len(best_free)):
                best, best_free, best_need = v, free, need
        for pick in combinations(best_free, best_need):
            recurse(chosen | set(pick), banned | (set(best_free) - set(pick)))

    recurse(set(), set())
    return sorted(solutions)


def path_dfs(vertices, edges, start, finish=None):
    """Independent spanning-path (or Hamiltonian-cycle when finish is
    None) enumeration by plain depth-first walk."""
    vertices = set(vertices)
    adjacency = {v: set() for v in vertices}
    for a, b in edges:
        if a in vertices and b in vertices:
            adjacency[a].add(b)
            adjacency[b].add(a)
    edge_list = sorted({edge(a, b) for a, b in edges})
    found = set()

    def walk(word):
        at = word[-1]
        if len(word) == len(vertices):
            if finish is None:
                if start in adjacency[at] and at != start:
                    chosen = [edge(u, w) for u, w in
                              zip(word, word[1:] + [start])]
                    found.add(vector(edge_list, chosen))
            elif at == finish:
                chosen = [edge(u, w) for u, w in zip(word, word[1:])]
                found.add(vector(edge_list, chosen))
            return
        for nxt in sorted(adjacency[at]):
            if nxt in word:
                continue
            if finish is not None and nxt == finish and \
                    len(word) + 1 < len(vertices):
                continue
            walk(word + [nxt])

    walk([start])
    return sorted(found)


def packings(vertices, edges, endpoints):
    """All spanning acyclic subgraphs of degree two except degree one at
    the given endpoints, grouped by the induced endpoint pairing."""
    edges = sorted({edge(a, b) for a, b in edges})
    endpoints = set(endpoints)
    target = {v: 1 if v in endpoints else 2 for v in vertices}
    result = {}
    for bits in degree_solutions(vertices, edges, target):
        sig = signature(vertices, edges, bits)
        if sig["cycles"] or sig["singletons"]:
            continue
        result.setdefault(tuple(sig["pairing"]), []).append(bits)
    if len(endpoints) == 2:
        a, b = sorted(endpoints)
        assert result.get(((a, b),), []) == path_dfs(vertices, edges, a, b)
    return result


def cycles(vertices, edges):
    """All Hamiltonian cycles as binary vectors, double enumerated."""
    edges = sorted({edge(a, b) for a, b in edges})
    rows = []
    for bits in degree_solutions(vertices, edges, {v: 2 for v in vertices}):
        chosen = [e for e, bit in zip(edges, bits) if bit]
        if len(components(vertices, chosen)[0]) == 1:
            rows.append(bits)
    assert rows == path_dfs(vertices, edges, min(vertices))
    return rows


def graph_audit(graph, extensions=None):
    """Simple cubic connected bipartite 2-deletion-connected check with
    optional oriented-sphere face audit and brace extension audit."""
    edges = sorted({edge(a, b) for a, b in map(tuple, graph["edges"])})
    vertices = sorted({v for e in edges for v in e})
    assert len(edges) == len(graph["edges"])
    assert all(a < b for a, b in edges)
    groups, adjacency = components(vertices, edges)
    assert len(groups) == 1
    assert all(len(adjacency[v]) == 3 for v in vertices)
    color = {vertices[0]: 0}
    queue = [vertices[0]]
    while queue:
        v = queue.pop()
        for w, _ in adjacency[v]:
            if w not in color:
                color[w] = 1 - color[v]
                queue.append(w)
            assert color[w] != color[v]
    for a, b in combinations(vertices, 2):
        rest_v = [v for v in vertices if v != a and v != b]
        rest_e = [e for e in edges if a not in e and b not in e]
        assert len(components(rest_v, rest_e)[0]) == 1
    if "faces" in graph:
        darts = []
        links = {v: {} for v in vertices}
        for face in graph["faces"]:
            assert len(face) == len(set(face))
            for j, v in enumerate(face):
                prv, nxt = face[j - 1], face[(j + 1) % len(face)]
                assert edge(v, nxt) in edges
                darts.append((v, nxt))
                assert prv not in links[v]
                links[v][prv] = nxt
        assert sorted(darts) == sorted(d for a, b in edges
                                       for d in ((a, b), (b, a)))
        assert len(vertices) - len(edges) + len(graph["faces"]) == 2
        for v, link in links.items():
            orbit, at = [], min(link)
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
                chosen = {i for i, bit in enumerate(record["matching"])
                          if bit}
            else:
                pair = tuple(sorted(record[:2]))
                chosen = set(record[2])
            pair_edges = tuple(sorted(edges[i] for i in pair))
            matching = {edges[i] for i in chosen}
            assert len(matching) == len(chosen) == len(vertices) // 2
            assert set(pair_edges) <= matching
            assert not set(pair_edges[0]) & set(pair_edges[1])
            assert sorted(v for e in matching for v in e) == vertices
            got.add(pair_edges)
        assert got == wanted
    return {"vertices": len(vertices), "edges": len(edges),
            "matching_extensions":
            len(extensions) if extensions is not None else None}
