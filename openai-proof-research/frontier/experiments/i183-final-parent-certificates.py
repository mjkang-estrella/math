"""Independent facial-arc and 626 matching checks on authorized retained data.

No child Python is loaded. Authentication reuses the current parent
validator; graph and matching algorithms below are separately implemented.
"""
import itertools
import json
import runpy
from collections import Counter
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
AUTH = runpy.run_path(str(EXP / "i183-final-parent-validate.py"))
TYPES = [
    ((0, 2), ((0, 2),)), ((1, 2), ((1, 2),)),
    ((1, 4), ((1, 4),)), ((2, 4), ((2, 4),)),
    ((0, 1, 2, 3), ((0, 2), (1, 3))), ((0, 1, 2, 3), ((0, 3), (1, 2))),
    ((0, 1, 3, 4), ((0, 3), (1, 4))),
    ((0, 2, 3, 4), ((0, 2), (3, 4))), ((0, 2, 3, 4), ((0, 3), (2, 4))),
    ((1, 2, 3, 4), ((1, 2), (3, 4))), ((1, 2, 3, 4), ((1, 4), (2, 3))),
]


def load(name):
    return json.loads((EXP / name).read_bytes())


def edge(a, b):
    return tuple(sorted((a, b)))


def structure(vertices, edges):
    """Union-find components plus incidence counts, including zero degrees."""
    parent = {v: v for v in vertices}
    degree = dict.fromkeys(vertices, 0)
    def root(v):
        while parent[v] != v:
            v = parent[v]
        return v
    for a, b in edges:
        parent[root(a)] = root(b)
        degree[a] += 1
        degree[b] += 1
    groups = {}
    for v in vertices:
        groups.setdefault(root(v), []).append(v)
    return list(groups.values()), degree


def facial_checks(payload):
    raw = load("i169_bridge_independence/audit-attempt-02.json")
    selected = {r["index"]: r for r in raw["rows"]}
    catalogue = load("i166_affine_span_braces/bracegen-graphs.json")
    graphs = {}
    def collect(obj):
        if isinstance(obj, dict):
            if "edges" in obj and "faces" in obj:
                graphs[tuple(sorted(map(tuple, obj["edges"])))] = obj
            for value in obj.values():
                collect(value)
        elif isinstance(obj, list):
            for value in obj:
                collect(value)
    collect(catalogue)
    checked = []
    for saved in payload["results"]["indexed"]:
        raw = selected[saved["index"]]
        edges = sorted(map(tuple, raw["parent_edges"]))
        faces = graphs[tuple(edges)]["faces"]
        vertices = {v for e in edges for v in e}
        darts = Counter((a, b) for f in faces for a, b in zip(f, f[1:] + f[:1]))
        assert darts == Counter({(a, b): 1 for u, v in edges for a, b in ((u, v), (v, u))})
        assert len(vertices) - len(edges) + len(faces) == 2
        assert all(len(set(f)) == len(f) for f in faces)
        u, v, x, y = raw["labels"][:4]
        deleted = {edge(u, v), edge(x, y)}
        relevant = [f for f in faces if deleted <= {
            edge(a, b) for a, b in zip(f, f[1:] + f[:1])}]
        assert len(relevant) == 1
        f = relevant[0]
        words, vectors = [], []
        for start, end in ((u, x), (v, y)):
            i = f.index(start)
            direction = -1 if edge(start, f[(i + 1) % len(f)]) in deleted else 1
            word = [start]
            while word[-1] != end:
                i = (i + direction) % len(f)
                assert f[i] not in word and edge(word[-1], f[i]) not in deleted
                word.append(f[i])
            z = [0] * len(edges)
            for j, (a, b) in enumerate(zip(word, word[1:])):
                z[edges.index(edge(a, b))] = 1 if j % 2 == 0 else -1
            words.append(word)
            vectors.append(z)
        actual = saved["arc_geometry"]
        assert actual["face"] == f and actual["words"] == words
        assert actual["lengths"] == [len(w) - 1 for w in words]
        assert set(words[0]).isdisjoint(words[1]) and set(sum(words, [])) == set(f)
        vectors.append([a + b for a, b in zip(*vectors)])
        assert actual["vectors"] == dict(zip(("Pux", "Pvy", "D11"), vectors))
        checked.append(saved["index"])
    assert checked == AUTH["ORDER"][:12]
    return checked


def enumerate_matchings(vertices, edges):
    incidence = {v: [e for e in edges if v in e] for v in vertices}
    def visit(open_set, chosen):
        if not open_set:
            yield tuple(sorted(chosen))
            return
        v = min(open_set)
        for e in incidence[v]:
            if set(e) <= open_set:
                yield from visit(open_set - set(e), chosen + [e])
    return list(visit(set(vertices), []))


def reduction_checks(payload):
    old = load("i177_adjacent_port_surgery/experiment-attempt-03.json")
    graph = old["child"]["graph"]
    info = old["fiveport"]
    X, Y = info["X"], info["Y"]
    xp = [13, 19, 20, 30, 31]
    cut = [(1, 13), (5, 19), (6, 20), (28, 30), (29, 31)]
    E = sorted(map(tuple, graph["edges"]))
    xe = [e for e in E if set(e) <= set(X)]
    assert info["xe"] == list(map(list, xe))
    adjacency = {v: [b if a == v else a for a, b in xe if v in (a, b)] for v in X}
    P = []
    def paths(word):
        if len(word) == len(X):
            if word[-1] == xp[1]:
                used = {edge(a, b) for a, b in zip(word, word[1:])}
                P.append(tuple(int(e in used) for e in xe))
            return
        for w in adjacency[word[-1]]:
            if w not in word and (w != xp[1] or len(word) + 1 == len(X)):
                paths(word + [w])
    paths([xp[0]])
    P.sort()
    assert len(P) == len(set(P)) == 5
    faces = [f for f in graph["faces"] if len(f) == 4]
    patches = []
    for f, g in itertools.combinations(faces, 2):
        ef = {edge(a, b) for a, b in zip(f, f[1:] + f[:1])}
        eg = {edge(a, b) for a, b in zip(g, g[1:] + g[:1])}
        if len(ef & eg) != 1 or not set(f + g) <= set(X) or set(f + g) & set(xp):
            continue
        patches.append((sorted(ef ^ eg), next(iter(ef & eg))))
    assert len(patches) == 3
    checks, results = 0, []
    for boundary, chord in patches:
        removed = {v for e in boundary for v in e}
        remaining = sorted(set(X + Y) - removed)
        ee = [e for e in E if not set(e) & removed]
        continuations = [e for e in E if len(set(e) & removed) == 1]
        for pi, p in enumerate(P):
            q = tuple(1 - b if e in boundary else b for e, b in zip(xe, p))
            if q not in P:
                continue
            A = [e for e in boundary if p[xe.index(e)]]
            forced = [e for e in boundary if e not in A] + [chord] + continuations
            groups, deg = structure(set(v for e in forced for v in e), forced)
            fixed = sorted(tuple(sorted(v for v in group if deg[v] == 1)) for group in groups)
            assert len(fixed) == 2 and all(len(pair) == 2 for pair in fixed)
            matchings = enumerate_matchings(remaining, ee)
            counts = dict(total=len(matchings), hamiltonian=0, controlled=0, lost_P=0,
                          lost_D=0, parallel_pairing=0, with_closed_components=0)
            controlled, hit = [], Counter()
            for m in matchings:
                checks += 1
                full = set(m) | set(A)
                H = [e for e in E if e not in full]
                hg, hd = structure(X + Y, H)
                assert set(hd.values()) == {2}
                hprime = [e for e in ee if e not in m]
                groups, deg = structure(remaining, hprime)
                assert set(deg.values()) <= {1, 2}
                closed = any(all(deg[v] == 2 for v in g) for g in groups)
                pairs = sorted(tuple(sorted(v for v in g if deg[v] == 1))
                               for g in groups if any(deg[v] == 1 for v in g))
                assert len(pairs) == 2
                assert (len(hg) == 1) == (not closed and pairs != fixed)
                if closed:
                    counts["with_closed_components"] += 1
                elif pairs == fixed:
                    counts["parallel_pairing"] += 1
                else:
                    counts["hamiltonian"] += 1
                    groups, deg = structure(X, [e for e in H if e in xe])
                    local_pair = tuple(sorted(tuple(sorted(xp.index(v) for v in g if deg[v] == 1))
                                              for g in groups))
                    used = tuple(i for i, e in enumerate(cut) if e in H)
                    local_type = (used, local_pair)
                    if local_type in TYPES:
                        counts["controlled"] += 1
                        hit[str(TYPES.index(local_type))] += 1
                        controlled.append(sorted(full))
                    else:
                        assert local_type in (((0, 1), ((0, 1),)),
                                              ((0, 1, 3, 4), ((0, 1), (3, 4))))
                        counts["lost_P" if used == (0, 1) else "lost_D"] += 1
            saved = next(r for r in payload["results"]["reduction"]["instances"]
                         if r["patch_boundary"] == list(map(list, boundary)) and r["p_index"] == pi)
            assert counts == saved["matchings"] and dict(hit) == saved["fibres_hit"]
            assert json.loads(json.dumps(sorted(controlled))) == saved["controlled_matchings"]
            results.append({"p_index": pi, "q_index": P.index(q), "counts": counts,
                            "controlled_set_matches": True})
    assert checks == 626 and len(results) == 6
    return results


if __name__ == "__main__":
    before = AUTH["authenticate"]()
    payload = load("i183_cptp_finalization/mandatory-01.json")
    result = {"status": "PASS", "facial_controls": facial_checks(payload),
              "matching_instances": reduction_checks(payload), "matching_checks": 626,
              "implementation": "Fresh parent face traversal, union-find, path DFS and exact cover",
              "scope": "Only authorized retained controls; no universal survival proof"}
    assert AUTH["authenticate"]() == before
    with (EXP / "i183-final-parent-certificates.json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: 12 independently reconstructed facial controls and all 626 matching checks")
