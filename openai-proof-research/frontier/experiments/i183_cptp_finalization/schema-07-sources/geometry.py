"""Fresh facial reconstruction from frozen rotations and mathematical definitions.

Loaded in the authenticated same-I183 exact namespace. No ancestor Python.
"""


def embedding(edges, faces):
    vertices = sorted({v for e in edges for v in e})
    assert edges == sorted(set(edges)) and all(a != b for a, b in edges)
    darts, turn = set(), {v: {} for v in vertices}
    for face in faces:
        assert len(face) >= 4 and len(face) == len(set(face))
        for i, v in enumerate(face):
            a, b = face[i-1], face[(i+1) % len(face)]
            assert edge(v, b) in edges and (v, b) not in darts
            darts.add((v, b))
            assert a not in turn[v]
            turn[v][a] = b
    assert darts == {(a, b) for u, v in edges for a, b in ((u, v), (v, u))}
    assert len(vertices) - len(edges) + len(faces) == 2
    for v, successor in turn.items():
        assert len(successor) == 3 and set(successor) == set(successor.values())
        at, seen = min(successor), set()
        while at not in seen:
            seen.add(at)
            at = successor[at]
        assert at == min(successor) and seen == set(successor)
    groups, adj = components(vertices, edges)
    assert len(groups) == 1
    color, todo = {vertices[0]: 0}, [vertices[0]]
    while todo:
        v = todo.pop()
        for w, _ in adj[v]:
            if w not in color:
                color[w] = 1-color[v]
                todo.append(w)
            assert color[w] != color[v]
    for removed in combinations(vertices, 2):
        rest = set(vertices)-set(removed)
        assert len(components(sorted(rest), [e for e in edges
                    if set(e) <= rest])[0]) == 1
    return {"vertices": len(vertices), "edges": len(edges),
            "faces": len(faces), "sphere_rotation": True,
            "bipartite": True, "three_connected": True}


def facial_arcs(edges, faces, labels):
    u, v, x, y = labels[:4]
    deleted = {edge(u, v), edge(x, y)}
    candidates = [f for f in faces if deleted <= {
        edge(a, b) for a, b in zip(f, f[1:]+f[:1])}]
    assert len(candidates) == 1
    f = candidates[0]
    kept = [edge(a, b) for a, b in zip(f, f[1:]+f[:1])
            if edge(a, b) not in deleted]
    groups, adj = components(f, kept)
    assert len(groups) == 2
    words, vectors = [], []
    for start, end in ((u, x), (v, y)):
        word, prev, at = [start], None, start
        while at != end:
            nxt = [w for w, _ in adj[at] if w != prev]
            assert len(nxt) == 1
            prev, at = at, nxt[0]
            assert at not in word
            word.append(at)
        assert len(word) % 2 == 0
        out = [0]*len(edges)
        for j, (a, b) in enumerate(zip(word, word[1:])):
            out[edges.index(edge(a, b))] = (-1)**j
        words.append(word)
        vectors.append(tuple(out))
    assert set(words[0]).isdisjoint(words[1])
    assert set(words[0]+words[1]) == set(f)
    return {"face": f, "words": words, "lengths": [len(w)-1 for w in words],
            "vectors": dict(zip(("Pux", "Pvy", "D11"),
                               vectors+[plus(*vectors)]))}


def graph_by_edges(read_json, wanted):
    key = {tuple(e) for e in wanted}
    data = read_json("frontier/experiments/i166_affine_span_braces/bracegen-graphs.json")
    found = []
    def visit(obj):
        if isinstance(obj, dict):
            if "faces" in obj and "edges" in obj and {
                    tuple(e) for e in obj["edges"]} == key:
                found.append(obj)
            for value in obj.values():
                visit(value)
        elif isinstance(obj, list):
            for value in obj:
                if isinstance(value, (list, dict)):
                    visit(value)
    visit(data)
    assert found, ("embedding missing", wanted)
    return found[0]


def check_extensions(edges, records):
    vertices = sorted({v for e in edges for v in e})
    required = {p for p in combinations(range(len(edges)), 2)
                if set(edges[p[0]]).isdisjoint(edges[p[1]])}
    seen = set()
    for item in records:
        if isinstance(item, dict):
            pair, matching = tuple(item["pair"]), item["matching"]
        else:
            assert len(item) == 3
            pair, matching = tuple(item[:2]), item[2]
        # Historical records use either edge indices or edge endpoint pairs.
        if matching and isinstance(matching[0], list):
            matching = [edges.index(tuple(e)) for e in matching]
        if pair and isinstance(pair[0], list):
            pair = tuple(edges.index(tuple(e)) for e in pair)
        pair = tuple(sorted(pair))
        assert pair in required and pair not in seen
        seen.add(pair)
        assert set(pair) <= set(matching) and len(set(matching)) == len(matching)
        assert sorted(v for i in matching for v in edges[i]) == vertices
    assert seen == required
    return len(seen)


def determinant(rows):
    a = [list(map(Fraction, row)) for row in rows]
    n, out = len(a), Fraction(1)
    assert all(len(row) == n for row in a)
    for j in range(n):
        p = next((i for i in range(j, n) if a[i][j]), None)
        if p is None:
            return Fraction(0)
        if p != j:
            a[p], a[j] = a[j], a[p]
            out = -out
        den = a[j][j]
        out *= den
        for i in range(j+1, n):
            q = a[i][j]/den
            a[i] = [x-q*y for x, y in zip(a[i], a[j])]
    assert rank(rows) == n
    return out
