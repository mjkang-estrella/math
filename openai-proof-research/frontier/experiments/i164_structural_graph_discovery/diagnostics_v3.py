"""I164 finite evidence. Standard library only; returns JSON-safe data."""
import importlib.util
import itertools
from fractions import Fraction
from pathlib import Path

HERE = Path(__file__).resolve().parent


def load(name):
    spec = importlib.util.spec_from_file_location("i164_" + name, HERE / (name + ".py"))
    module = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(module)
    return module


def rank(rows):
    a = [[Fraction(x) for x in row] for row in rows]
    if not a:
        return 0
    r = 0
    for j in range(len(a[0])):
        q = next((i for i in range(r, len(a)) if a[i][j]), None)
        if q is None:
            continue
        a[q], a[r] = a[r], a[q]
        value = a[r][j]
        a[r] = [x / value for x in a[r]]
        for i in range(r + 1, len(a)):
            value = a[i][j]
            a[i] = [x - value * y for x, y in zip(a[i], a[r])]
        r += 1
    return r


def path_edges(path):
    return {tuple(sorted(e)) for e in zip(path, path[1:])}


def path_count(n, edges, start, end, forbidden):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        if (a, b) not in forbidden:
            adj[a].add(b)
            adj[b].add(a)

    def rec(v, seen):
        if v == end:
            return int(len(seen) == n)
        return sum(rec(w, seen | {w}) for w in adj[v] - seen)
    return rec(start, {start})


def two_factors(n, edges):
    adj = [[] for _ in range(n)]
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)

    def rec(unused, matching):
        if not unused:
            yield set(edges) - set(matching)
            return
        a = min(unused)
        for b in adj[a]:
            if b in unused:
                yield from rec(unused - {a, b}, matching + [tuple(sorted((a, b)))])
    yield from rec(set(range(n)), [])


def components(n, edges):
    adj = [set() for _ in range(n)]
    for a, b in edges:
        adj[a].add(b)
        adj[b].add(a)
    todo = set(range(n))
    result = []
    while todo:
        found = {min(todo)}
        stack = list(found)
        while stack:
            for w in adj[stack.pop()] - found:
                found.add(w)
                stack.append(w)
        todo -= found
        result.append(found)
    return result


def expansion_identity(n, edges, terminals, expansion):
    base = load("explore")
    u, v, x, y = terminals
    e, f = tuple(sorted((u, v))), tuple(sorted((x, y)))
    hc = base.cycles(n, edges)
    n00 = sum(e not in c and f not in c for c in hc)
    p_ux = path_count(n, edges, u, x, {e, f})
    p_vy = path_count(n, edges, v, y, {e, f})
    d11 = 0
    for factor in two_factors(n, edges):
        cs = components(n, factor)
        if len(cs) == 2 and e in factor and f in factor:
            d11 += int(not any(u in c and x in c for c in cs))
    new_count = len(base.cycles(n + 4, expansion))
    assert new_count == len(hc) - n00 + p_ux + p_vy + d11
    return dict(n=n, old=len(hc), new=new_count, N00=n00,
                Pux=p_ux, Pvy=p_vy, D11=d11, gain=new_count-len(hc))


def main():
    base = load("explore")
    expand = load("expansion_probe")
    prisms = []
    expansion_checks = []
    for m in range(4, 18, 2):
        n = 2 * m
        edges = base.edges_of_prism(m)
        hc = base.cycles(n, edges)
        assert base.three_connected(n, edges)
        assert len(hc) == m + 2
        affine_rank = rank([[int(e in c) - int(e in hc[0]) for e in edges]
                            for c in hc[1:]])
        assert affine_rank == m + 1
        # A prescribed rung-horizontal-rung P4 has a unique completion.
        p0 = path_edges([m, 0, 1, m+1])
        assert sum(p0 <= c for c in hc) == 1
        p4_tests = 0
        adj = [set() for _ in range(n)]
        for a, b in edges:
            adj[a].add(b)
            adj[b].add(a)
        for a in range(n):
            for b in adj[a]:
                for c in adj[b] - {a}:
                    for d in adj[c] - {a, b}:
                        p = path_edges([a, b, c, d])
                        assert any(p <= h for h in hc)
                        p4_tests += 1
        if m >= 10:
            j = m // 2
            j = j if j % 2 else j + 1
            p1 = path_edges([m+j, j, j+1, m+j+1])
            assert not any(p0 | p1 <= c for c in hc)
            factors = list(two_factors(n, edges))
            assert any(p0 | p1 <= factor for factor in factors)
            # Two distant top-rim edges of opposite index parity.
            j_odd = j if j % 2 else j + 1
            deleted = {(0, 1), (j_odd, j_odd+1)}
            assert not any(not (deleted & c) for c in hc)
        prisms.append(dict(m=m, n=n, h=len(hc), affine_rank=affine_rank,
                           directed_P4_checks=p4_tests,
                           minimum_P4_completions=1))
        if m <= 10:
            # Cofacial top-rim edges at even index difference.
            u, v, y, x = 0, 1, 2, 3
            new = expand.expanded(n, edges, u, v, x, y)
            expansion_checks.append(expansion_identity(n, edges, [u, v, x, y], new))
    # Finite exact Vandermonde nonsingularity for the exponential-order bridge.
    vandermonde = 0
    for size in range(1, 7):
        for ts in itertools.combinations(range(-4, 5), size):
            assert rank([[t ** j for t in ts] for j in range(size)]) == size
            vandermonde += 1
    return dict(prisms=prisms, expansion_identity=expansion_checks,
                vandermonde_cases=vandermonde,
                scope="finite diagnostics, not proof of Q164 or worldwide novelty")
