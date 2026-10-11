"""Independent parent checks using plain path DFS and matching recursion."""
import json
from collections import Counter
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i171_square_switch_weight"


def read(name):
    return json.loads((BASE / name).read_text())


def edge(u, v):
    return tuple(sorted((u, v)))


def paths(edges, start, end, vertices, spanning=True):
    adj = {v: [] for v in vertices}
    for u, v in edges:
        if u in adj and v in adj:
            adj[u].append(v)
            adj[v].append(u)

    def walk(v, used, chosen):
        if v == end:
            if not spanning or used == vertices:
                yield frozenset(chosen)
            return
        for n in adj[v]:
            if n not in used:
                yield from walk(n, used | {n}, chosen + [edge(v, n)])

    return walk(start, {start}, [])


def cycles(edges, vertices):
    root = min(vertices)
    neighbors = [b if a == root else a for a, b in edges if root in (a, b)]
    result = set()
    for i, u in enumerate(neighbors):
        for v in neighbors[i + 1:]:
            for p in paths(edges, u, v, vertices - {root}):
                result.add(p | {edge(root, u), edge(root, v)})
    return result


def components(edges, vertices):
    unseen = set(vertices)
    result = []
    while unseen:
        reached = {unseen.pop()}
        while True:
            more = {v for e in edges if reached.intersection(e) for v in e} - reached
            if not more:
                break
            reached |= more
        unseen -= reached
        result.append(reached)
    return result


def terminals(graph, step):
    face, i, j = step
    f = graph["faces"][face]
    return f[i], f[(i + 1) % len(f)], f[(j + 1) % len(f)], f[j]


def main():
    cert = read("weight-obstruction-attempt-01.json")["witnesses"]["two_component_forbidden_weight"]
    graph = cert["graph"]
    es = list(map(tuple, graph["edges"]))
    vertices = {v for e in es for v in e}
    u, v, x, y = terminals(graph, cert["step"])
    e, f, a, c = edge(u, v), edge(x, y), edge(u, x), edge(v, y)
    hc = cycles(es, vertices)
    w = dict(zip(es, map(Fraction, cert["w"])))
    weight = lambda s: sum(w[z] for z in s)
    c0 = frozenset(z for z, bit in zip(es, cert["C0"]) if bit)
    n = frozenset(z for z, bit in zip(es, cert["N"]) if bit)
    assert c0 in hc and n in hc
    assert all(weight(h) - weight(c0) == int(e not in h and f not in h) for h in hc)
    factor = frozenset(map(tuple, cert["factor_edges"]))
    switch = (n - {a, c}) | {e, f}
    for z in (factor, switch):
        assert z <= set(es)
        assert Counter(v for t in z for v in t) == Counter({v: 2 for v in vertices})
        assert len(components(z, vertices)) == 2 and z not in hc
    assert factor != switch
    assert weight(factor) - weight(c0) == Fraction(-1, 2)
    assert weight(switch) - weight(c0) == Fraction(1, 14)
    assert sorted(map(len, components(factor, vertices))) == [16, 16]

    def matchings(left):
        if not left:
            yield frozenset()
            return
        p = min(left)
        for q in sorted(left - {p}):
            z = edge(p, q)
            if z in w:
                for rest in matchings(left - {p, q}):
                    yield rest | {z}

    ms = set(matchings(vertices))
    assert len(ms) == 1007
    extending_pairs = {frozenset((a, b)) for m in ms for a in m for b in m if a != b}
    all_pairs = {frozenset((a, b)) for a in es for b in es if not set(a) & set(b)}
    assert extending_pairs == all_pairs and len(all_pairs) == 1032

    guide = read("guide-attempt-01.json")
    g = guide["graph"]
    ges = list(map(tuple, g["edges"]))
    vs = {v for e in ges for v in e}
    u, v, x, y = terminals(g, guide["row"]["step"])
    e, f = edge(u, v), edge(x, y)
    k = set(ges) - {e, f}
    ghc = cycles(ges, vs)
    survivors = [h for h in ghc if e in h or f in h]
    old = [h for h in ghc if e not in h and f not in h]
    new = [list(paths(k, u, x, vs)), list(paths(k, v, y, vs))]
    covers = set()
    for p in paths(k, u, v, vs, spanning=False):
        used = {t for z in p for t in z}
        if x in used or y in used:
            continue
        for q in paths(k, x, y, vs - used):
            covers.add(p | q)
    new.append(list(covers))
    assert len(old) == 2 and len(survivors) == 22
    assert [len(z) for z in new] == [4, 4, 14]
    wb = dict(zip(ges, guide["bridge_separator"]["w"]))
    dot = lambda z: sum(wb[e] for e in z)
    assert len({dot(h) for h in survivors}) == 1
    assert all(len({dot(h) for h in cl}) == 1 for cl in new)
    bdot = sum(w * b for w, b in zip(guide["bridge_separator"]["w"], guide["bridge_separator"]["b"]))
    assert bdot == guide["bridge_separator"]["dot"] == 10
    assert sum(dot(cl[0]) for cl in new) + 2 * (wb[e] + wb[f]) - 3 * dot(survivors[0]) == 10
    assert abs(dot(old[0]) - dot(old[1])) == 8
    result = {"status": "PASS", "C171_hamiltonian_cycles": len(hc),
              "C171_two_component_weight": "-1/2", "C171_square_switch_weight": "1/14",
              "perfect_matchings": len(ms), "disjoint_edge_pairs_extended": len(all_pairs),
              "index431_hamiltonian_cycles": len(ghc), "index431_new_class_sizes": [4, 4, 14],
              "index431_bridge_pairing": bdot, "index431_old_difference_absolute_pairing": 8,
              "implementation": "Independent parent DFS and matching recursion; no ancestor or child Python imported."}
    with (BASE.parent / "i171-parent-certificates.json").open("x") as stream:
        json.dump(result, stream, indent=2, sort_keys=True)
        stream.write("\n")
    print(json.dumps(result, indent=2))


if __name__ == "__main__":
    main()
