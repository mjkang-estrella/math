"""Fresh targeted controls and local topology checks. No new graph tests."""
from fractions import Fraction
from itertools import combinations, product
import json

# The runner injects authenticated math181 primitives and a frozen JSON reader.
ORDER = [0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539, 431]
OLD = "frontier/experiments/"
TYPES = [
    ((0, 2), ((0, 2),)), ((1, 2), ((1, 2),)),
    ((1, 4), ((1, 4),)), ((2, 4), ((2, 4),)),
    ((0, 1, 2, 3), ((0, 2), (1, 3))),
    ((0, 1, 2, 3), ((0, 3), (1, 2))),
    ((0, 1, 3, 4), ((0, 3), (1, 4))),
    ((0, 2, 3, 4), ((0, 2), (3, 4))),
    ((0, 2, 3, 4), ((0, 3), (2, 4))),
    ((1, 2, 3, 4), ((1, 2), (3, 4))),
    ((1, 2, 3, 4), ((1, 4), (2, 3))),
]


def eq(a, b, label="equality"):
    assert json.loads(json.dumps(a)) == json.loads(json.dumps(b)), label


def tuples(rows):
    return [tuple(r) for r in rows]


def embed(edges, local, row):
    d = dict(zip(local, row))
    return tuple(d.get(e, 0) for e in edges)


def sumrows(rows, n):
    return add(*rows) if rows else (0,)*n


def selected_families(edges, uvxy):
    vertices = sorted({v for e in edges for v in e})
    u, v, x, y = uvxy
    e, f = edge(u, v), edge(x, y)
    cyc = cycles(vertices, edges)
    families = {"N"+str(a)+str(b): [r for r in cyc if (r[edges.index(e)], r[edges.index(f)]) == (a, b)]
                for a, b in product(range(2), repeat=2)}
    ke = [h for h in edges if h not in (e, f)]
    for name, endpoints, pairing in [
            ("Pux", (u, x), (edge(u, x),)), ("Pvy", (v, y), (edge(v, y),)),
            ("D11", (u, v, x, y), tuple(sorted((edge(u, v), edge(x, y)))))]:
        rows = packings(vertices, ke, endpoints).get(pairing, [])
        families[name] = [embed(edges, ke, r) for r in rows]
    return cyc, families


def control(edges, uvxy, expected, retained=None):
    edges = sorted(map(tuple, edges))
    vertices = sorted({v for e in edges for v in e})
    u, v, x, y = uvxy
    e, f = edge(u, v), edge(x, y)
    cyc, fam = selected_families(edges, uvxy)
    if retained is not None:
        for name, rows in retained.items():
            rows = sorted(vector(edges, r) if r and isinstance(r[0], list) else tuple(r) for r in rows)
            eq(fam[name], rows, "complete family "+name)
    surv = sorted(fam["N10"]+fam["N01"]+fam["N11"])
    assert all(fam.values())
    L, V = differences(surv), differences(fam["N00"])
    L0 = sum((differences(fam[k]) for k in ("N10", "N01", "N11")), [])
    U = sum((differences(fam[k]) for k in ("Pux", "Pvy", "D11")), [])
    P, Q, D = [fam[k][0] for k in ("Pux", "Pvy", "D11")]
    A, B, C, N = [fam[k][0] for k in ("N10", "N01", "N11", "N00")]
    twice = tuple(2 if h in (e, f) else 0 for h in edges)
    b = add(P, Q, D, twice, scale(-3, surv[0]))
    beta = add(P, Q, D, twice, scale(-1, A), scale(-1, B), scale(-1, C))
    c = add(N, scale(-1, A), scale(-1, B), C)
    for name, row in [("b", b), ("beta", beta), ("c", c)]:
        eq(row, expected[name], name)
        assert all(sum(row[j] for j, h in enumerate(edges) if vtx in h) == 0 for vtx in vertices)
    assert beta[edges.index(e)] == beta[edges.index(f)] == 0
    assert rank(L+[sub(b, beta)]) == rank(L)
    assert rank([tuple(r[edges.index(h)] for h in (e, f)) for r in L]) == 2
    goodspace, residualspace, res = [], [], {}
    for name, ends in [("Pux", (u, x)), ("Pvy", (v, y)), ("D11", (u, v, x, y))]:
        q = tuple(expected["residuals"][name]["q"])
        if name != "D11":
            support = [h for h, bit in zip(edges, q) if bit]
            vs = sorted({vtx for h in support for vtx in h})
            parts, adj = components(vs, support)
            assert len(parts) == 1
            assert sorted(vtx for vtx in vs if len(adj[vtx]) == 1) == sorted(ends)
            assert all(sum(q[j] for j, h in enumerate(edges) if vtx in h) ==
                       (1 if vtx in ends else 0) for vtx in vertices)
            assert all(bit in (-1, 0, 1) for bit in q)
        else:
            eq(q, add(res["Pux"]["q"], res["Pvy"]["q"]), "double arc")
        good = [r for r in fam["N00"] if sub(r, q) in fam[name]]
        residual = [r for r in fam[name] if add(r, q) not in fam["N00"]]
        anchor = sub(good[0], q) if good else fam[name][0]
        directions = [sub(r, anchor) for r in residual]
        if not good:
            directions = [sub(r, anchor) for r in fam[name]]
        res[name] = {"q": q, "good": good, "residual": residual,
                     "anchor": anchor, "residual_directions": directions}
        eq(res[name], expected["residuals"][name], "residual "+name)
        goodspace += differences(good)
        residualspace += directions
        assert rank(differences(fam[name])) == rank(differences(good)+directions)
    assert rank(U+goodspace+residualspace) == rank(U) == rank(goodspace+residualspace)
    rL, rLU = rank(L), rank(L+U)
    ell = rank(differences(cyc))-rL
    t = rLU-rL
    eta = rank(L+U+[b])-rLU
    deltaV = rank(L0+V)-rank(L0+goodspace)
    deltaR = rank(L0+goodspace+residualspace)-rank(L0+goodspace)
    epsilon = rank(L0+V+[c])-rank(L0+V)
    assert ell-t == deltaV+epsilon-deltaR
    assert rL == 2+rank(L0) and rLU == 2+rank(L0+U)
    row = {"counts": {k: len(vv) for k, vv in fam.items()},
           "arcs": [sum(bool(x) for x in res[k]["q"]) for k in ("Pux", "Pvy")],
           "dg": rank(differences(cyc)), "rankL": rL, "rankL0": rank(L0),
           "rankU": rank(U), "rankUV": rank(U+V), "ell": ell, "t": t, "eta": eta,
           "delta_V": deltaV, "delta_R": deltaR, "epsilon": epsilon}
    eq(row, expected["row"], "control ranks")
    for name, result in [("V_subset_U", rank(U+V) == rank(U)),
                         ("V_subset_LU", rank(L+U+V) == rLU)]:
        assert result == expected[name]
    return {"row": row, "b": b, "beta": beta, "c": c, "residuals": res,
            "families": fam, "cycles": cyc}


def step_vertices(graph, step):
    face = graph["faces"][step[0]]
    i, j = step[1:]
    return [face[i], face[(i+1) % len(face)], face[(j+1) % len(face)], face[j]]


def k6(expected, uniform):
    k, n, j = 6, 5, 3
    T = lambda i: 12+i
    B = lambda i: 18+i
    tr = lambda a, b: [T(i) for i in range(a, b+(1 if b >= a else -1), 1 if b >= a else -1)]
    br = lambda a, b: [B(i) for i in range(a, b+(1 if b >= a else -1), 1 if b >= a else -1)]
    p, q, s, t = 26, 27, 24, 25
    W, V = [T(1), B(1), B(2), T(2), T(3), B(3)], [T(1), T(2), B(2), B(3), T(3)]
    words = {
        "0": [tr(1, j)+[p, q]+tr(n-1, n)+br(n, 0)],
        "1a": [[B(0), B(1)]+V+[p, q, T(n-1), B(n-1), B(n), T(n)]],
        "1b": [[T(n), T(n-1), q, p]+tr(j, 1)+br(1, n)+[B(0)]],
        "2": [[T(n), T(n-1), B(n-1), B(n), B(0), B(1)]+V+[p, q]],
        "3": [[B(0), B(n), T(n), T(n-1)]+br(n-1, 1)+tr(1, j)+[p, q]],
        "4a": [W+[B(n-1), B(n), B(0)], [T(n), T(n-1), q, p]],
        "4b": [tr(1, j)+br(j, 0), [T(n), B(n), B(n-1), T(n-1), q, p]],
        "5": [W+[B(n-1), T(n-1), q, p], [T(n), B(n), B(0)]],
        "6(n-1)": [tr(1, j)+[p], [T(n), B(n)]+br(0, n-1)+[T(n-1), q]],
        "7Z": [W+[B(n-1), T(n-1), T(n), B(n), B(0)], [p, q]],
        "8": [tr(1, j)+[p], br(0, n)+[T(n), T(n-1), q]],
        "9": [[T(n), B(n), B(0)], [p]+tr(j, 1)+br(1, n-1)+[T(n-1), q]],
        "10a": [[T(n), B(n), B(n-1), T(n-1), q], [B(0), B(1)]+V+[p]],
        "10b": [[T(n), T(n-1), q], [B(0)]+br(n, 1)+tr(1, j)+[p]],
    }
    for r in range(1, j):
        words["6r"+str(r)] = [tr(1, r)+br(r, 0)+br(n, r+1)+tr(r+1, j)+[p], [T(n), T(n-1), q]]
        words["7r"+str(r)] = [tr(1, r)+br(r, 0), [p]+tr(j, r+1)+br(r+1, n)+[T(n), T(n-1), q]]
    eq(words, expected["words"], "U176 words")
    xe = sorted([edge(T(i), B(i)) for i in range(1, n+1)] +
                [edge(T(i), T(i+1)) for i in range(1, n) if i != j] +
                [edge(B(i), B((i+1) % (n+1))) for i in range(n+1)] +
                [edge(T(j), p), edge(p, q), edge(q, T(n-1))])
    ye = [(1, 7), (1, s), (2, 3), (2, 8), (2, t), (3, 4), (3, 9),
          (4, 5), (4, 10), (5, 11), (6, 7), (6, 11), (7, 8), (8, 9),
          (9, 10), (10, 11), (s, t)]
    cut = [(1, T(1)), (5, T(n)), (6, B(0)), (s, p), (t, q)]
    es = sorted(xe+ye+cut)
    local = {}
    for name, paths in words.items():
        assert sorted(v for path in paths for v in path) == sorted({v for e in xe for v in e})
        chosen = [edge(a, b) for path in paths for a, b in zip(path, path[1:])]
        assert set(chosen) <= set(xe)
        local[name] = vector(xe, chosen)
        witness_name = "6r4" if name == "6(n-1)" else name
        witness = next(w for w in uniform["local_witnesses"] if w["name"] == witness_name)
        eq([e for e, x in zip(xe, local[name]) if not x], witness["missing"], "omitted edges")
        state = witness["state"]
        ports = [T(1), T(n), B(0), p, q]
        eq(sorted(edge(ports.index(path[0]), ports.index(path[-1])) for path in paths), TYPES[state][1])
    selected = ["0", "1a", "2", "3", "4a", "5", "6r1", "7Z", "8", "9", "10a"]
    anchors = []
    for i, name in enumerate(selected):
        y = tuple(uniform["anchors"][i]["Y"])
        jy = TYPES[i][0]
        row = add(embed(es, xe, local[name]), embed(es, ye, y), vector(es, [cut[k] for k in jy]))
        sg = signature(sorted({v for e in es for v in e}), es, row)
        assert len(sg["cycles"]) == 1 and not sg["pairing"]
        assert row[es.index(cut[2])] or row[es.index((1, 7))]
        eq(row, uniform["anchors"][i]["cycle"])
        anchors.append(row)
    eq(anchors, expected["anchors"])
    dirs = [sub(local["6r"+str(r)], local["6(n-1)"]) for r in (1, 2)]
    dirs += [sub(local[a], local[b]) for a, b in [("1a", "1b"), ("4a", "4b"), ("7Z", "7r1")]]
    cols = [(13, 14), (14, 15), (16, 17), (26, 27), (18, 19)]
    minor = [[row[xe.index(e)] for e in cols] for row in dirs]
    eq(minor, expected["local_minor"])
    assert determinant(minor) == -2
    states = uniform["states"]
    im = [embed(es, ye, sub(states[1]["Y"][1], states[1]["Y"][0]))]
    im += [embed(es, ye, sub(states[4]["Y"][i], states[4]["Y"][0])) for i in (1, 2)]
    im += [sub(anchors[i], anchors[0]) for i in (1, 2, 3, 4, 5, 7)]
    cols = [(1, 7), (1, s), (2, 3), (2, 8), (3, 4), (4, 5), (5, 11), (6, 7), (s, t)]
    imat = [[r[es.index(e)] for e in cols] for r in im]
    assert determinant(imat) == 1
    eq(imat, [[int(x) for x in r] for r in expected["image_minor"]])
    return {"words": words, "anchors": anchors, "local_minor": minor, "image_minor": imat}


def presentation(data):
    es, xe, ye, cut = [list(map(tuple, data[k])) for k in ("edges", "xe", "ye", "cut")]
    X, Y, xp = data["X"], data["Y"], data["xp"]
    yp = [next(v for v in e if v in Y) for e in cut]
    complete = []
    all_products, survivors = set(), set()
    states = {}
    for size in (2, 4):
        for J in combinations(range(5), size):
            sides = []
            for vs, ee, ports in [(X, xe, xp), (Y, ye, yp)]:
                fam = packings(vs, ee, [ports[j] for j in J])
                relabelled = {tuple(sorted(edge(ports.index(a), ports.index(b)) for a, b in pairing)): rows
                              for pairing, rows in fam.items()}
                sides.append(relabelled)
            lx, ly = sides
            complete.append({"J": J, "local": [{"pairing": p, "packings": rr} for p, rr in sorted(lx.items())],
                             "exterior": [{"pairing": p, "packings": rr} for p, rr in sorted(ly.items())]})
            for px, xs in lx.items():
                for py, ys in ly.items():
                    if size == 4 and px == py:
                        continue
                    for a, b in product(xs, ys):
                        row = add(embed(es, xe, a), embed(es, ye, b), vector(es, [cut[j] for j in J]))
                        sg = signature(X+Y, es, row)
                        assert len(sg["cycles"]) == 1
                        all_products.add(row)
                        if 2 in J or b[ye.index((1, 7))]:
                            survivors.add(row)
                            key = (J, px)
                            state = states.setdefault(key, {"X": set(), "Y": set(), "py": py})
                            assert state["py"] == py
                            state["X"].add(a)
                            state["Y"].add(b)
    eq(complete, data["complete"], "all complete fibres including empties")
    assert len(all_products) == data["full"] == 64
    assert len(survivors) == data["survivors"] == 46
    assert set(states) == set(TYPES)
    xs, ys, anchors = [], [], []
    for i, key in enumerate(TYPES):
        state = states[key]
        a, b = sorted(state["X"]), sorted(state["Y"])
        eq(a, data["states"][i]["X"])
        eq(b, data["states"][i]["Y"])
        xs.append(a)
        ys.append(b)
        anchors.append(add(embed(es, xe, a[0]), embed(es, ye, b[0]), vector(es, [cut[j] for j in key[0]])))
    A = [sub(c, anchors[0]) for c in anchors]
    eq(A, data["A"])
    wx = sum(([embed(es, xe, r) for r in differences(a)] for a in xs), [])
    wy = [embed(es, ye, sub(ys[1][1], ys[1][0]))]
    wy += [embed(es, ye, sub(ys[4][i], ys[4][0])) for i in (1, 2)]
    lifts = [add(A[6], A[1], scale(-1, A[2]), scale(-1, A[5])),
             add(A[8], A[1], scale(-1, A[3]), scale(-1, A[5])),
             sub(A[9], add(A[1], A[7])),
             add(A[10], scale(-1, A[1]), scale(-1, A[4]), A[5], scale(-1, A[7]))]
    eq(lifts, data["lifts"])
    pi = [es.index(e) for e in ye+cut]
    assert all(not r[j] for r in lifts for j in pi)
    image = wy+[A[i] for i in (1, 2, 3, 4, 5, 7)]
    assert rank([tuple(r[j] for j in pi) for r in image]) == 9
    assert rank(wx) == 5 and rank(wy) == 3 and rank(wx+lifts) == 7
    assert rank(wx+wy+A) == rank(differences(sorted(survivors))) == 16
    residuals = []
    for co in data["completion"]:
        J = tuple(co["J"])
        target = add(xs[0][0], xs[2][0], scale(-1, xs[3][0]), scale(4, xs[4][0]), scale(-4, xs[5][0]))
        if len(J) == 4:
            target = add(target, scale(-1, xs[0][0]), xs[7][0])
        eq(target, co["target"])
        lift = sumrows([scale(Fraction(a), r) for a, r in zip(co["coordinates"], image)], len(es))
        # Every lost packing and every actual exterior completion is checked.
        relevant = next(c for c in complete if tuple(c["J"]) == J)
        pairing = ((0, 1),) if len(J) == 2 else ((0, 1), (3, 4))
        rows = next(c["packings"] for c in relevant["local"] if tuple(c["pairing"]) == pairing)
        for x in rows:
            full = add(embed(es, xe, x), embed(es, ye, co["exterior"]), vector(es, [cut[j] for j in J]))
            assert full in all_products and full not in survivors
            r = sub(sub(full, anchors[0]), lift)
            assert r == embed(es, xe, sub(x, target))
            residuals.append(tuple(int(v) for v in r))
    eq(sorted(set(residuals)), sorted(set(tuples(data["residuals"]))))
    # All 22 individual actual alternative anchors: kernel equality, not fixed coefficients after Y changes.
    changes = 0
    for i in range(11):
        for alt in xs[i][1:]:
            delta = embed(es, xe, sub(alt, xs[i][0]))
            assert rank(wx+[delta]) == 5
            changes += 1
        for alt in ys[i][1:]:
            delta = embed(es, ye, sub(alt, ys[i][0]))
            assert rank(wy+[delta]) == 3
            changes += 1
    assert changes == 22
    return {"edges": es, "xe": xe, "X": X, "xp": xp, "xs": xs, "ys": ys,
            "A": A, "wx": wx, "wy": wy, "lifts": lifts, "image": image,
            "complete": complete, "residuals": sorted(set(residuals)), "anchor_changes": changes}


def overlay_components(edges, a, b):
    delta = [e for e, x, y in zip(edges, a, b) if x != y]
    vs = sorted({v for e in delta for v in e})
    groups, adj = components(vs, delta)
    out = []
    for group in groups:
        chosen = [e for e in delta if e[0] in group]
        out.append((chosen, all(len(adj[v]) == 2 for v in group)))
    return out


def toggle(edges, row, chosen):
    selected = set(chosen)
    return tuple(1-x if e in selected else x for e, x in zip(edges, row))


def lock(pres, expected):
    X, xe, xp = pres["X"], pres["xe"], pres["xp"]
    P = packings(X, xe, xp[:2])[(edge(xp[0], xp[1]),)]
    s = pres["xs"][0][0]
    masks = singles = failures = 0
    record = []
    for i, p in enumerate(P):
        parts = overlay_components(xe, p, s)
        good = []
        for mask in range(1 << len(parts)):
            selected = sum((part[0] for j, part in enumerate(parts) if mask >> j & 1), [])
            a, b = toggle(xe, p, selected), toggle(xe, s, selected)
            sa, sb = signature(X, xe, a), signature(X, xe, b)
            assert add(a, b) == add(p, s)
            valid = not (sa["cycles"] or sb["cycles"] or sa["singletons"] or sb["singletons"])
            if valid:
                assert {a, b} == {p, s}
                good.append(mask)
            if mask.bit_count() == 1:
                singles += 1
                failures += not valid
            masks += 1
        record.append({"p": i, "components": [a for a, _ in parts], "valid_masks": good})
    assert (masks, singles, failures) == (18, 9, 8)
    eq(P, expected["P"])
    return P, {"masks": masks, "single_switches": singles, "cycle_failures": failures, "records": record}


def helpers(pres, P, parent_expected, calibration):
    xe, X = pres["xe"], pres["X"]
    identities = []
    for j, q in enumerate(P[1:], 1):
        for i, family in enumerate(pres["xs"]):
            for ui, u in enumerate(family):
                target = sub(add(P[0], u), q)
                if target in family:
                    chosen = [e for e, a, b in zip(xe, P[0], q) if a != b]
                    parts = overlay_components(xe, P[0], u)
                    whole = any(iscycle and set(es) == set(chosen) for es, iscycle in parts)
                    identities.append({"P_index": j, "state": i, "u_index": ui,
                                       "up_index": family.index(target), "changed_edges": chosen,
                                       "single_alternating_cycle": whole})
    eq(identities, parent_expected["solutions"], "parent exact identities")
    witnesses, rejected = [], []
    graph = set()
    overlays = moves = 0
    for pi, p in enumerate(P):
        for state, family in enumerate(pres["xs"]):
            for ui, u in enumerate(family):
                overlays += 1
                for ce, iscycle in overlay_components(xe, p, u):
                    if not iscycle:
                        continue
                    moves += 1
                    q, v = toggle(xe, p, ce), toggle(xe, u, ce)
                    assert add(p, u) == add(q, v)
                    sq, sv = signature(X, xe, q), signature(X, xe, v)
                    valid = q in P and v in family
                    item = {"p_index": pi, "state": state, "u_index": ui, "cycle_edges": ce}
                    if valid:
                        qi, vi = P.index(q), family.index(v)
                        graph.add(tuple(sorted((pi, qi))))
                        item.update(q_index=qi, v_index=vi)
                        witnesses.append(item)
                    else:
                        assert sq["cycles"], "Every retained failure is lost-output cyclic"
                        item.update(q=sq, v=sv)
                        rejected.append(item)
    assert (overlays, moves, len(witnesses), len(rejected)) == (130, 123, 24, 99)
    assert graph == {(0, 1), (1, 2), (2, 3), (3, 4)}
    for item in witnesses:
        assert any(all(old[k] == (list(v) if isinstance(v, tuple) else v)
                       for k, v in item.items() if k != "cycle_edges") and
                   old["cycle_edges"] == [list(e) for e in item["cycle_edges"]]
                   for old in calibration["witnesses"])
    exact = []
    for pi, qi in combinations(range(5), 2):
        for state, family in enumerate(pres["xs"]):
            for ui, vi in product(range(len(family)), repeat=2):
                if add(P[pi], family[ui]) != add(P[qi], family[vi]):
                    continue
                ce = [e for e, a, b in zip(xe, P[pi], P[qi]) if a != b]
                if any(cycle and set(part) == set(ce)
                       for part, cycle in overlay_components(xe, P[pi], family[ui])):
                    exact.append((pi, qi, state, ui, vi))
    assert len(exact) == 12
    assert sorted(exact) == sorted((w["p_index"], w["q_index"], w["state"], w["u_index"], w["v_index"])
                                  for w in witnesses if w["p_index"] < w["q_index"])
    for old in identities:
        if not old["single_alternating_cycle"]:
            assert not any(w["p_index"] == 0 and w["state"] == old["state"] and
                           w["u_index"] == old["u_index"] for w in witnesses)
    distances = [sum(a != b for a, b in zip(p, P[4])) for p in P]
    assert distances == [8, 8, 8, 6, 0]
    wx = sum((differences(family) for family in pres["xs"]), [])
    ranks = [rank(differences(P)), rank(wx), rank(wx+differences(P))]
    assert ranks == [4, 5, 5]
    return {"parent_identities": identities, "overlays": overlays, "cycle_moves": moves,
            "witnesses": witnesses, "rejected": rejected, "graph": sorted(graph),
            "exact_forward": exact, "distances": distances, "ranks": ranks}


def mandatory():
    old = read_json(OLD+"i180_survivor_helper_connectivity/mandatory-attempt-02.json")
    source = read_json(OLD+"i169_bridge_independence/audit-attempt-02.json")["rows"]
    out = {"order": [], "controls": []}
    for index, expected in zip(ORDER, old["controls"]):
        data = source[index]
        assert data["index"] == expected["index"] == index
        out["controls"].append(control(data["parent_edges"], data["labels"][:4], expected, data["classes"]))
        out["order"].append(index)
    c171 = read_json(OLD+"i172_prescribed_square_switch/mandatory-attempt-01.json")["C171"]
    es = sorted(map(tuple, c171["graph"]["edges"]))
    uvxy = step_vertices(c171["graph"], c171["row"]["step"])
    out["C171"] = control(es, uvxy, old["C171"])
    out["C171"]["graph"] = graph_check(c171["graph"], c171["extensions"])
    w, C0, F, T = [list(map(Fraction, c171[k])) for k in ("w", "C0", "F", "T")]
    assert F != T
    for name, r, value in [("F", F, Fraction(1, 14)), ("T", T, Fraction(-1, 2))]:
        assert sum(a*b for a, b in zip(w, sub(r, C0))) == value
        sg = signature(sorted({v for e in es for v in e}), es, r)
        assert len(sg["cycles"]) == 2
    pre = tuple(old["C171"]["switch"]["precycle"])
    square = [tuple(e) for e in old["C171"]["switch"]["square"]]
    assert toggle(es, pre, square) == tuple(F) and pre in out["C171"]["cycles"]
    out["order"].append("C171")
    g = read_json(OLD+"i172_prescribed_square_switch/cut-octagons-attempt-01.json")["records"]
    out["G6_G10"] = []
    for size, expected in zip((6, 10), old["G6_G10"]):
        data = next(a for a in g if a["L"] == size)
        z = control(data["graph"]["edges"], step_vertices(data["graph"], data["row"]["step"]), expected, data["families"])
        es = sorted(map(tuple, data["graph"]["edges"]))
        vs = sorted({v for e in es for v in e})
        matchings = factors(vs, es, {v: 1 for v in vs})
        pair = list(map(tuple, expected["nonbrace_pair"]))
        assert not any(all(r[es.index(e)] for e in pair) for r in matchings)
        z["nonbrace_pair"] = pair
        z["perfect_matchings"] = len(matchings)
        out["G6_G10"].append(z)
    out["order"].append("G6/G10")
    p8 = read_json(OLD+"i175_affected_prism_exterior/experiment-attempt-01.json")["first_children"][0]
    out["first_P8"] = control(p8["graph"]["edges"], p8["uvxy"], old["first_P8"], p8["families"])
    out["first_P8"]["graph"] = graph_check(p8["graph"], p8["brace"]["extensions"])
    out["order"].append("first_P8")
    uniform = read_json(OLD+"i176_uniform_five_port_rank/uniform-attempt-02.json")["checks"][0]
    assert uniform["k"] == 6
    out["I176_k6"] = k6(old["I176_k6"], uniform)
    out["order"].append("I176_k6")
    child = read_json(OLD+"i177_adjacent_port_surgery/experiment-attempt-03.json")
    data = child["child"]
    out["I177"] = control(data["graph"]["edges"], data["uvxy"], old["I177"], data["families"])
    out["I177"]["graph"] = graph_check(data["graph"], data["brace"]["extensions"])
    initial = child["initial"]
    out["I177_initial"] = control(initial["graph"]["edges"], initial["uvxy"], old["I177_initial"], initial["families"])
    # Build the actual product basis for the absorption checks, with presentation
    # reconstruction recorded at its required next control position.
    d = old["I178"]
    es, xe, ye = [list(map(tuple, d[k])) for k in ("edges", "xe", "ye")]
    xs = [tuples(s["X"]) for s in d["states"]]
    A = tuples(d["A"])
    Xb = [embed(es, xe, sub(xs[1][1], xs[1][0]))]
    Xb += [embed(es, xe, sub(xs[5][i], xs[5][0])) for i in range(1, 5)]
    Yb = tuples(d["Ybasis"])
    lifts = tuples(d["lifts"])
    base = Xb+Yb+[A[i] for i in (1, 2, 3, 4, 5, 7)]+lifts[:2]
    assert rank(base) == 16
    oldes = sorted(map(tuple, initial["graph"]["edges"]))

    def tau(r):
        row = embed(es, oldes, r)
        row = list(row)
        a, b = r[oldes.index((1, 2))], r[oldes.index((13, 14))]
        for e, x in [((1, 28), a), ((2, 29), a), ((13, 30), b), ((14, 31), b),
                     ((28, 29), -a), ((30, 31), -b), ((28, 30), 0), ((29, 31), 0)]:
            row[es.index(e)] = x
        return tuple(row)
    for equation in old["I177_absorption"]["equations"]:
        target = tau(equation["old_direction"])
        eq(target, equation["transport"])
        assert target == sumrows([scale(Fraction(c), b) for c, b in zip(equation["coefficients"], base)], len(es))
    olddiff = differences(out["I177_initial"]["cycles"])
    assert rank([tau(r) for r in olddiff]) == rank(olddiff) == 14
    rhs = add(scale(5, Xb[0]), *[scale(-1, r) for r in Xb[1:]], lifts[0], scale(2, lifts[1]))
    assert scale(3, lifts[2]) == scale(3, lifts[3]) == rhs
    cols = child["actual_survivor_minor"]["columns"]
    sb = data["survivor_basis"]
    for r in sb:
        assert add(r, data["survivor_anchor"]) in out["I177"]["cycles"]
    assert determinant([[r[i] for i in cols] for r in sb]) == 2
    out["I177_absorption"] = old["I177_absorption"]
    out["order"].append("I177_child_absorption")
    pres = presentation(d)
    out["I178"] = {k: v for k, v in pres.items() if k not in ("xs", "ys")}
    out["order"].append("I178_relations_completion")
    P, out["I179_lock"] = lock(pres, old["I179_lock"])
    out["order"].append("I179_lock")
    cal = read_json(OLD+"i180_survivor_helper_connectivity/calibration-attempt-02.json")
    out["helper"] = helpers(pres, P, old["parent_helper"], cal)
    out["order"] += ["parent_helper", "I180_helpergraph"]
    out["status"] = "PASS"
    return out


def perfect_pairings(items):
    if not items:
        yield []
        return
    a = items[0]
    for i, b in enumerate(items[1:], 1):
        for rest in perfect_pairings(items[1:i]+items[i+1:]):
            yield [(a, b)]+rest


def topology():
    """Formal segment incidence verification, not tests of additional graphs."""
    cycle = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]
    halfA = [(0, 1), (2, 3), (4, 5)]
    halfB = [(1, 2), (3, 4), (0, 5)]
    chord = [(0, 3)]
    eq(signature(list(range(6)), sorted(cycle+chord), vector(sorted(cycle+chord), halfA+chord))["pairing"],
       [(1, 2), (4, 5)])
    eq(signature(list(range(6)), sorted(cycle+chord), vector(sorted(cycle+chord), halfB+chord))["pairing"],
       [(1, 2), (4, 5)])
    results = []
    for ports in ([6, 7], [6, 7, 8, 9]):
        nodes = [1, 2, 4, 5]+ports
        for segments in perfect_pairings(nodes):
            # Keep parallel edges: these encode closed components, not one edge.
            quotient = segments+[(1, 2), (4, 5)]
            groups, adj = components(nodes, quotient)
            cyclic = [g for g in groups if all(len(adj[v]) == 2 for v in g)]
            pairing = sorted(tuple(sorted(v for v in g if v in ports))
                             for g in groups if any(v in ports for v in g))
            reattachments = []
            for half in (halfA, halfB):
                edges = segments+half+chord
                gs, aa = components([0, 3]+nodes, edges)
                cyc = sum(all(len(aa[v]) == 2 for v in g) for g in gs)
                pp = sorted(tuple(sorted(v for v in g if v in ports))
                            for g in gs if any(v in ports for v in g))
                assert cyc == len(cyclic) and pp == pairing
                reattachments.append({"cycles": cyc, "pairing": pp})
            results.append({"ports": ports, "segments": segments, "quotient_cycles": len(cyclic),
                            "pairing": pairing, "reattachments": reattachments})
    # Explicit unsimplified contractions: loops and parallel pairs must be cycles.
    for es in [[(1, 1)], [(1, 2), (1, 2)]]:
        vs = sorted({v for e in es for v in e})
        gs, aa = components(vs, es)
        assert len(gs) == 1 and all(len(aa[v]) == 2 for v in vs)
    return {"status": "PASS", "scope": "Formal local incidence lemma, no added graph tests",
            "rows": results, "rows_count": len(results),
            "routing_A": [[1, 0, 3, 2], [4, 5]],
            "routing_B": [[1, 2], [4, 3, 0, 5]],
            "E181": "UNRESOLVED"}
