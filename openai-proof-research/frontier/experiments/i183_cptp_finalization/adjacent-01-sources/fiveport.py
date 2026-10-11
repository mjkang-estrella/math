"""Fresh complete retained five-port products and exact linear presentation."""
from collections import defaultdict


def linear_combination(coefficients, rows):
    return tuple(sum(Fraction(c)*r[j] for c, r in zip(coefficients, rows))
                 for j in range(len(rows[0])))


def nullspace_rows(rows):
    """Coefficient vectors for all linear relations among the given rows."""
    a = [list(map(Fraction, col)) for col in zip(*rows)]
    n, pivot, r = len(rows), [], 0
    for j in range(n):
        p = next((i for i in range(r, len(a)) if a[i][j]), None)
        if p is None:
            continue
        a[r], a[p] = a[p], a[r]
        den = a[r][j]
        a[r] = [x/den for x in a[r]]
        for i in range(len(a)):
            if i != r:
                z = a[i][j]
                a[i] = [x-z*y for x, y in zip(a[i], a[r])]
        pivot.append(j)
        r += 1
    result = []
    for j in range(n):
        if j in pivot:
            continue
        v = [Fraction(0)]*n
        v[j] = 1
        for i, p in enumerate(pivot):
            v[p] = -a[i][j]
        assert not any(linear_combination(v, rows))
        result.append(v)
    assert len(result)+rank(rows) == n
    return result


def complete_side(vertices, edges, ports, J):
    groups = defaultdict(list)
    for bits in family(vertices, edges, [ports[j] for j in J]):
        sig = signature(vertices, [e for e, b in zip(edges, bits) if b])
        pairing = tuple(sorted(edge(ports.index(a), ports.index(b))
                               for a, b in sig["paths"]))
        groups[pairing].append(bits)
    return dict(sorted(groups.items()))


def build_system(read_json, child):
    stored = read_json(P177+"experiment-attempt-03.json")["fiveport"]
    edges = [tuple(e) for e in stored["graph"]["edges"]]
    X = list(range(13, 28))+[30, 31]
    Y = list(range(1, 12))+[28, 29]
    cut = [(1, 13), (5, 19), (6, 20), (28, 30), (29, 31)]
    xp, yp = [13, 19, 20, 30, 31], [1, 5, 6, 28, 29]
    xe = [e for e in edges if set(e) <= set(X)]
    ye = [e for e in edges if set(e) <= set(Y)]
    assert sorted(xe+ye+cut) == edges
    assert stored["X"] == X and stored["Y"] == Y
    assert stored["xe"] == normalize(xe) and stored["ye"] == normalize(ye)
    def embed(bits, subedges):
        return tuple(bits[subedges.index(e)] if e in subedges else 0 for e in edges)
    def glue(x, y, J):
        return plus(embed(x, xe), embed(y, ye),
                    tuple(int(e in [cut[j] for j in J]) for e in edges))
    all_records, local, exterior = [], {}, {}
    all_cycles, surviving = set(), set()
    for k in (2, 4):
        for J in combinations(range(5), k):
            xx = complete_side(X, xe, xp, J)
            yy = complete_side(Y, ye, yp, J)
            local[J], exterior[J] = xx, yy
            all_records.append({"J": J,
                "local": [{"pairing": p, "packings": v} for p, v in xx.items()],
                "exterior": [{"pairing": p, "packings": v} for p, v in yy.items()]})
            for px, xs in xx.items():
                for py, ys in yy.items():
                    if k == 4 and px == py:
                        continue
                    for x, y in product(xs, ys):
                        z = glue(x, y, J)
                        sig = signature(X+Y, [e for e, b in zip(edges, z) if b])
                        assert len(sig["cycles"]) == 1 and not sig["paths"]
                        all_cycles.add(z)
                        if 2 in J or y[ye.index((1, 7))]:
                            surviving.add(z)
    assert normalize(all_records) == stored["all_families"]
    assert sorted(all_cycles) == child["cycles"]
    expected_survivors = sorted(child["families"]["N10"]+
                               child["families"]["N01"]+child["families"]["N11"])
    assert sorted(surviving) == expected_survivors
    states = []
    for i, st in enumerate(stored["states"]):
        J, px, py = tuple(st["J"]), tuple(map(tuple, st["px"])), tuple(map(tuple, st["py"]))
        xs = local[J][px]
        ys = [y for y in exterior[J][py] if 2 in J or y[ye.index((1, 7))]]
        assert normalize(xs) == st["X"] and normalize(ys) == st["Y"]
        products = sorted(glue(x, y, J) for x, y in product(xs, ys))
        assert normalize(products) == st["products"]
        anchor = glue(xs[0], ys[0], J)
        assert list(anchor) == st["anchor"]
        states.append({"J": J, "px": px, "py": py, "X": xs, "Y": ys,
                       "anchor": anchor, "products": products})
    assert sum(len(st["products"]) for st in states) == 46
    wx = [embed(z, xe) for st in states for z in differences(st["X"])]
    wy = [embed(z, ye) for st in states for z in differences(st["Y"])]
    anchors = [st["anchor"] for st in states]
    A = [minus(a, anchors[0]) for a in anchors]
    lifts = [plus(A[6], A[1], times(-1, A[2]), times(-1, A[5])),
             plus(A[8], A[1], times(-1, A[3]), times(-1, A[5])),
             plus(A[9], times(-1, A[1]), times(-1, A[7])),
             plus(A[10], times(-1, A[1]), times(-1, A[4]), A[5],
                  times(-1, A[7]))]
    xb = [embed(minus(states[1]["X"][1], states[1]["X"][0]), xe)] + [
        embed(minus(states[5]["X"][j], states[5]["X"][0]), xe) for j in range(1, 5)]
    yb = [embed(minus(states[1]["Y"][1], states[1]["Y"][0]), ye)] + [
        embed(minus(states[4]["Y"][j], states[4]["Y"][0]), ye) for j in (1, 2)]
    image = yb+[A[j] for j in (1, 2, 3, 4, 5, 7)]
    basis = xb+image+lifts[:2]
    assert (rank(wx), rank(wy), rank(basis)) == (5, 3, 16)
    assert rank(wx+wy+A[1:]+differences(sorted(surviving))) == 16
    proj = [j for j, e in enumerate(edges) if e not in xe]
    return dict(edges=edges, X=X, Y=Y, xe=xe, ye=ye, cut=cut, xp=xp, yp=yp,
                local=local, exterior=exterior, states=states, wx=wx, wy=wy,
                A=A, lifts=lifts, xb=xb, yb=yb, image=image, basis=basis,
                proj=proj, embed=embed, glue=glue, all_records=all_records)


def adjacent(read_json):
    data = read_json(P177+"experiment-attempt-03.json")
    ref = read_json(REF)
    initial = control(from_graph(data["initial"]["graph"], "I177_initial",
                                data["initial"]["uvxy"]), ref["I177_initial"])
    child = control(from_graph(data["child"]["graph"], "I177",
                              data["child"]["uvxy"]), ref["I177"])
    oldedges = [tuple(e) for e in data["initial"]["graph"]["edges"]]
    edges = [tuple(e) for e in data["child"]["graph"]["edges"]]
    removed = [(1, 2), (13, 14)]
    inserted = [(1, 28), (2, 29), (13, 30), (14, 31),
                (28, 29), (28, 30), (29, 31), (30, 31)]
    assert sorted(set(oldedges)-set(removed) | set(inserted)) == edges
    assert check_extensions(edges, data["child"]["brace"]["extensions"]) == 900
    S = build_system(read_json, child)
    assert [[Fraction(x) for x in row] for row in data["actual_ambient_basis"]] == S["basis"]
    def tau(z):
        a, b = [z[oldedges.index(e)] for e in removed]
        values = {(1,28):a, (2,29):a, (13,30):b, (14,31):b,
                  (28,29):-a, (30,31):-b, (28,30):0, (29,31):0}
        return tuple(z[oldedges.index(e)] if e in oldedges else values[e] for e in edges)
    oldspan = differences(initial["cycles"])
    transported = [tau(z) for z in oldspan]
    assert rank(oldspan) == rank(transported) == 14
    equations = []
    for equation in data["old_defect_absorption"]:
        z = tuple(equation["old_direction"])
        assert z in oldspan or rank(oldspan+[z]) == 14
        transport = tau(z)
        assert list(transport) == equation["transport"]
        assert linear_combination(equation["coefficients"], S["basis"]) == transport
        assert all(sum(transport[j] for j, e in enumerate(edges) if v in e) == 0
                   for v in S["X"]+S["Y"])
        equations.append({"old_direction": z, "transport": transport,
                          "coefficients": equation["coefficients"]})
    minor = data["actual_survivor_minor"]
    survivors = sorted(child["families"]["N10"]+child["families"]["N01"]+
                       child["families"]["N11"])
    anchor = tuple(data["child"]["survivor_anchor"])
    actual = [tuple(z) for z in data["child"]["survivor_basis"]]
    assert anchor in survivors and all(plus(anchor, z) in survivors for z in actual)
    matrix = [[z[j] for j in minor["columns"]] for z in actual]
    assert matrix == minor["matrix"] and determinant(matrix) == 2
    return {"status": "PASS", "initial": initial, "child": child,
            "extensions": 900, "transport_rank": 14, "equations": equations,
            "actual_minor": matrix}, S


def presentation(read_json, S):
    ref = read_json(REF)["I178"]
    wx, yb, A, K, proj = (S[k] for k in ("wx", "yb", "A", "lifts", "proj"))
    G = yb+A[1:]
    projection = lambda z: tuple(z[j] for j in proj)
    rel = nullspace_rows([projection(z) for z in G])
    lift = [linear_combination(z, G) for z in rel]
    assert rank(lift+K+wx) == rank(K+wx) == 7
    assert len(rel) == 4 and all(not any(projection(z)) for z in K)
    for key, actual in (("A", A), ("lifts", K), ("wx", wx), ("wy", S["wy"]),
                        ("image", S["image"])):
        assert normalize(actual) == ref[key], key
    xb = S["xb"]
    rhs = plus(times(5, xb[0]), *[times(-1, z) for z in xb[1:]], K[0], times(2, K[1]))
    assert times(3, K[2]) == times(3, K[3]) == rhs
    count = 0
    anchors = [st["anchor"] for st in S["states"]]
    for i, st in enumerate(S["states"]):
        for side in ("X", "Y"):
            for z in st[side][1:]:
                aa = anchors[:]
                aa[i] = S["glue"](z if side == "X" else st["X"][0],
                                 z if side == "Y" else st["Y"][0], st["J"])
                gg = yb+[minus(z, aa[0]) for z in aa[1:]]
                rr = nullspace_rows([projection(z) for z in gg])
                kk = [linear_combination(z, gg) for z in rr]
                assert rank(wx+kk) == rank(wx+K+kk) == 7
                count += 1
    assert count == 22
    aa = [S["glue"](st["X"][-1], st["Y"][-1], st["J"]) for st in S["states"]]
    yy = [plus(yb[0], yb[1]), plus(yb[1], yb[2]), yb[2]]
    gg = yy+[minus(z, aa[0]) for z in aa[1:]]
    kk = [linear_combination(z, gg) for z in nullspace_rows([projection(z) for z in gg])]
    assert rank(wx+kk) == rank(wx+K+kk) == 7
    xs = [S["embed"](st["X"][0], S["xe"]) for st in S["states"]]
    targetP = plus(xs[0], xs[2], times(-1,xs[3]), times(4,xs[4]), times(-4,xs[5]))
    targetD = plus(xs[2], times(-1,xs[3]), times(4,xs[4]), times(-4,xs[5]), xs[7])
    residuals = []
    for J, pairing, target in (((0,1), ((0,1),), targetP),
                               ((0,1,3,4), ((0,1),(3,4)), targetD)):
        packs = S["local"][J][pairing]
        partners = [y for py, ys in S["exterior"][J].items()
                    if len(J)==2 or py != pairing for y in ys]
        assert len(partners) == 3
        for x in packs:
            residual = minus(S["embed"](x,S["xe"]),target)
            residuals.append(residual)
            for y in partners:
                d = minus(S["glue"](x,y,J),anchors[0])
                assert rank(G+[minus(d,residual)]) == rank(G)
    assert normalize(residuals) == ref["residuals"]
    return {"status":"PASS", "relations": [[str(x) for x in z] for z in rel],
            "lifts":K, "kernel_rank":7, "anchor_changes":count,
            "simultaneous_anchor_basis_change":True, "residuals":residuals,
            "complete_fibres":S["all_records"]}
