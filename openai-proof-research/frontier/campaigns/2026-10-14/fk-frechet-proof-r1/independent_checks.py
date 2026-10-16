"""Independent exact current-response stress checks, not an asymptotic proof.

No candidate imports. Only standard library. Run with python -B.
"""
from fractions import Fraction as F
from itertools import combinations
import json


def solve(a, b):
    z = [[F(x) for x in row] + [F(y)] for row, y in zip(a, b)]
    for j in range(len(z)):
        p = next(i for i in range(j, len(z)) if z[i][j])
        z[j], z[p] = z[p], z[j]
        d = z[j][j]
        z[j] = [x/d for x in z[j]]
        for i in range(len(z)):
            if i != j:
                d = z[i][j]
                z[i] = [x-d*y for x, y in zip(z[i], z[j])]
    return [row[-1] for row in z]


def poisson(vertices, edges, current, pole):
    rest = [v for v in vertices if v != pole]
    a = {v: {w: F(0) for w in vertices} for v in vertices}
    for v, w, r in edges:
        if v == w:
            continue
        a[v][v] += 1/r
        a[w][w] += 1/r
        a[v][w] -= 1/r
        a[w][v] -= 1/r
    out = solve([[a[v][w] for w in rest] for v in rest], [current[v] for v in rest])
    return {pole: F(0), **dict(zip(rest, out))}


def check_block_responses():
    # Planar K4, theta block, nested bridges, parallel edges, loops at poles
    # and at other attachment vertices. Each block attaches at one old vertex.
    raw = [
        (0, list(combinations(range(4), 2))),
        (1, [(1, 4)]),
        (4, [(4, 5), (5, 6), (6, 4), (4, 6)]),
        (6, [(6, 7)]),
        (2, [(2, 8), (2, 8), (2, 8)]),
        (0, [(0, 0)]),
        (4, [(4, 4)]),
        (7, [(7, 7)]),
    ]
    blocks = []
    edges = []
    for j, (pole, pairs) in enumerate(raw):
        loc = [(v, w, F(2+3*j+i, 1+i % 3)) for i, (v, w) in enumerate(pairs)]
        ids = set(range(len(edges), len(edges)+len(loc)))
        edges.extend(loc)
        blocks.append((pole, loc, ids))
    vertices = list(range(9))
    degree = {v: 0 for v in vertices}
    for v, w, _ in edges:
        degree[v] += 1
        degree[w] += 1
    projections = []
    for pole, loc, ids in blocks:
        bv = {x for v, w, _ in loc for x in (v, w)}
        proj = {}
        for x in bv:
            seen = {x}
            todo = [x]
            while todo:
                v = todo.pop()
                for i, (a, b, _) in enumerate(edges):
                    if i in ids:
                        continue
                    w = b if a == v else a if b == v else None
                    if w is not None and w not in seen:
                        seen.add(w)
                        todo.append(w)
            assert seen.intersection(bv) == {x}
            assert not set(proj).intersection(seen)
            proj.update({v: x for v in seen})
        assert set(proj) == set(vertices)
        projections.append(proj)
    count = 0
    for mass in [degree, {v: v*v+1 for v in vertices}]:
        total = sum(mass.values())
        # These currents span all zero-total injections and exercise the
        # actual weighted generator through g(v)=current(v)/mass(v).
        for target in vertices[1:]:
            current = {v: F((v == target)-(v == 0)) for v in vertices}
            full = poisson(vertices, edges, current, 0)
            mean = sum(mass[v]*full[v] for v in vertices)/total
            full = {v: full[v]-mean for v in vertices}
            assembled = {v: F(0) for v in vertices}
            for (pole, loc, _), proj in zip(blocks, projections):
                bv = sorted(set(proj.values()))
                local_current = {x: sum(current[v] for v in vertices if proj[v] == x) for x in bv}
                h = poisson(bv, loc, local_current, pole)
                mean = sum(mass[v]*h[proj[v]] for v in vertices)/total
                for v in vertices:
                    assembled[v] += h[proj[v]]-mean
            assert full == assembled
            # Direct Kirchhoff residual verifies the solution independently.
            for v in vertices:
                outgoing = sum((full[v]-full[b if a == v else a])/r
                               for a, b, r in edges if (a == v or b == v) and a != b)
                assert outgoing == current[v]
            count += 1
    return count


def degeneracies():
    # One bridge and h loops at its far end: far mass is 2h+1, total 2h+2.
    # Solve the 2x2 generator eigenvalue directly; h=10^12 stresses a
    # far component occupying almost all mass, with no graph allocation.
    cases = []
    for h in [0, 1, 17, 10**12]:
        r = F(37, 5)
        mf = 2*h+1
        positive_eigenvalue = (1+F(1, mf))/r
        tau = 1/positive_eigenvalue
        assert tau == r*mf/F(mf+1)
        if h:
            assert tau != r*mf
        cases.append({'far_loops': h, 'tau': str(tau), 'far_mass': mf})
    # Two parallel edges: solve injection equation and compare to the
    # harmonic effective resistance. Neither edge is an independent trap.
    e = [(0, 1, F(7)), (0, 1, F(101))]
    v = poisson([0, 1], e, {0: F(-1), 1: F(1)}, 0)
    assert v[1] == F(707, 108)
    # Equal masses 2: relaxation time is exactly that resistance.
    assert v[1] < min(e[0][2], e[1][2])
    # Single vertex and arbitrary loops: grounded space is empty.
    assert poisson([0], [(0, 0, F(999))], {0: F(0)}, 0) == {0: F(0)}
    return cases


if __name__ == '__main__':
    print(json.dumps({'status': 'PASS_FINITE_SUPPORT_ONLY',
                      'independent_kirchhoff_basis_responses': check_block_responses(),
                      'large_branch_cases': degeneracies(),
                      'parallel_and_single_vertex_checks': True,
                      'asymptotic_proof': False}, indent=2))
