"""Exact primitives, newly implemented for the continuation.

Same-I183 math183.py informed the interfaces and algorithms. No older
implementation is used. In particular, elimination uses a*row-b*pivot,
the second rank really transposes, and traversal keeps edge identities.
"""
from fractions import Fraction
from itertools import combinations, product
from math import gcd, lcm


def edge(a, b):
    return tuple(sorted((a, b)))


def plus(*rows):
    return tuple(sum(x) for x in zip(*rows))


def minus(a, b):
    return tuple(x - y for x, y in zip(a, b))


def times(k, row):
    return tuple(k * x for x in row)


def differences(rows):
    return [minus(x, rows[0]) for x in rows[1:]] if rows else []


def rank_integer(rows):
    grid = []
    for row in rows:
        fs = list(map(Fraction, row))
        den = lcm(*(x.denominator for x in fs))
        grid.append([int(x * den) for x in fs])
    r = 0
    for col in range(len(grid[0]) if grid else 0):
        p = next((i for i in range(r, len(grid)) if grid[i][col]), None)
        if p is None:
            continue
        grid[r], grid[p] = grid[p], grid[r]
        a = grid[r][col]
        for i in range(r + 1, len(grid)):
            b = grid[i][col]
            if b:
                grid[i] = [a * x - b * y for x, y in zip(grid[i], grid[r])]
                div = gcd(*grid[i])
                if div:
                    grid[i] = [x // div for x in grid[i]]
        r += 1
    return r


def rank_fraction(rows):
    # Reverse the rows of the actual transpose, not a second transpose.
    grid = [list(map(Fraction, col)) for col in reversed(list(zip(*rows)))]
    r = 0
    for col in range(len(grid[0]) if grid else 0):
        pivot = next((i for i in range(r, len(grid)) if grid[i][col]), None)
        if pivot is None:
            continue
        grid[r], grid[pivot] = grid[pivot], grid[r]
        den = grid[r][col]
        grid[r] = [x / den for x in grid[r]]
        for i in range(len(grid)):
            if i != r:
                factor = grid[i][col]
                grid[i] = [x - factor * y for x, y in zip(grid[i], grid[r])]
        r += 1
    return r


def rank(rows):
    rows = list(rows)
    assert not rows or all(len(x) == len(rows[0]) for x in rows)
    a, b = rank_integer(rows), rank_fraction(rows)
    assert a == b, (a, b)
    return a


def components(vertices, edges):
    adjacency = {v: [] for v in vertices}
    for i, (a, b) in enumerate(edges):
        adjacency[a].append((b, i))
        adjacency[b].append((a, i))
    unseen, groups = set(vertices), []
    while unseen:
        todo, group = [min(unseen)], set()
        while todo:
            v = todo.pop()
            if v not in group:
                group.add(v)
                todo.extend(w for w, _ in adjacency[v] if w not in group)
        unseen -= group
        groups.append(sorted(group))
    return groups, adjacency


def signature(vertices, chosen):
    groups, adjacency = components(vertices, chosen)
    assert all(len(a) <= 2 for a in adjacency.values())
    paths, cycles, singles = [], [], []
    for group in groups:
        ends = [v for v in group if len(adjacency[v]) == 1]
        if not adjacency[group[0]]:
            assert len(group) == 1
            singles.append(group[0])
        elif ends:
            assert len(ends) == 2
            paths.append(tuple(ends))
        else:
            # Loops contribute degree two; parallel pairs are cycles.
            assert all(len(adjacency[v]) == 2 for v in group)
            cycles.append(group)
    return {"paths": sorted(paths), "cycles": cycles, "singletons": singles}


def factors(vertices, edges, target):
    """Complete simple-graph binary degree solutions, constraint recursion."""
    assert all(a != b for a, b in edges) and len(set(edges)) == len(edges)
    incidence = {v: {i for i, e in enumerate(edges) if v in e}
                 for v in vertices}
    out = set()

    def rec(chosen, banned):
        while True:
            changed = False
            for v in vertices:
                free = incidence[v] - chosen - banned
                need = target[v] - len(incidence[v] & chosen)
                if need < 0 or need > len(free):
                    return
                if free and need in (0, len(free)):
                    if need:
                        chosen = chosen | free
                    else:
                        banned = banned | free
                    changed = True
            if not changed:
                break
        if len(chosen | banned) == len(edges):
            out.add(tuple(int(i in chosen) for i in range(len(edges))))
            return
        free = min((incidence[v] - chosen - banned for v in vertices
                    if incidence[v] - chosen - banned), key=len)
        i = min(free)
        rec(chosen | {i}, banned)
        rec(chosen, banned | {i})
    rec(set(), set())
    return sorted(out)


def dfs_spanning(vertices, edges, start, finish=None):
    """Independent vertex-walk enumeration for cycles and single paths."""
    vs = set(vertices)
    adj = {v: [] for v in vertices}
    positions = {e: i for i, e in enumerate(edges)}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    out = set()

    def rec(word, seen):
        if len(word) == len(vs):
            if finish is None and start in adj[word[-1]]:
                w = word + [start]
            elif finish is not None and word[-1] == finish:
                w = word
            else:
                return
            chosen = {positions[edge(a, b)] for a, b in zip(w, w[1:])}
            out.add(tuple(int(i in chosen) for i in range(len(edges))))
            return
        for w in adj[word[-1]]:
            if w not in seen and (w != finish or len(word) + 1 == len(vs)):
                rec(word + [w], seen | {w})
    rec([start], {start})
    return sorted(out)


def family(vertices, edges, endpoints=(), pairing=None):
    endpoints = tuple(endpoints)
    result = []
    for bits in factors(vertices, edges,
                        {v: 1 if v in endpoints else 2 for v in vertices}):
        selected = [e for e, bit in zip(edges, bits) if bit]
        sig = signature(vertices, selected)
        if endpoints:
            if sig["cycles"] or sig["singletons"]:
                continue
            if pairing is not None and sig["paths"] != sorted(pairing):
                continue
        elif len(sig["cycles"]) != 1 or sig["singletons"] or sig["paths"]:
            continue
        result.append(bits)
    if len(endpoints) == 2:
        assert result == dfs_spanning(vertices, edges, *sorted(endpoints))
    elif not endpoints:
        assert result == dfs_spanning(vertices, edges, min(vertices))
    return result


def unit_tests():
    """Algebra and abstract incidence tests, not new graph experiments."""
    matrices = [
        ([], 0), ([[]], 0), ([[0, 0]], 0),
        ([[1, 2], [2, 4]], 1),  # old draft's wrong elimination pivot
        ([[2, 4, 6], [1, 2, 3]], 1),
        ([[1, 0, 2], [0, 1, 3]], 2),
        ([[Fraction(1, 2), 1], [1, 2]], 1),
    ]
    for rows, expected in matrices:
        assert rank(rows) == expected
    count = 0
    # Exhaustive tiny matrix test has a separate determinant oracle.
    for a, b, c, d in product((-1, 0, 1), repeat=4):
        expected = 2 if a*d != b*c else int(any((a, b, c, d)))
        assert rank([[a, b], [c, d]]) == expected
        count += 1
    assert signature([0], [(0, 0)])["cycles"] == [[0]]
    assert signature([0, 1], [(0, 1), (0, 1)])["cycles"] == [[0, 1]]
    assert signature([0], [])["singletons"] == [0]
    assert signature([0, 1, 2], [(0, 1), (1, 2)])["paths"] == [(0, 2)]
    return {"ranks": len(matrices) + count, "incidence_cases": 4,
            "status": "PASS", "scope": "unit tests, no new graph population"}
