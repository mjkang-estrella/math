"""Fresh I182 targeted controls and the controlled three-edge extension diagnostic.

No new graph tests: every computation runs on retained, frozen, authenticated
data. The runner injects exact math182 primitives and a frozen JSON reader.
"""
from fractions import Fraction
from itertools import combinations, product
import json

ORDER = [0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539, 431]
OLD = "frontier/experiments/"
I181M = OLD + "i181_six_cycle_helper/mandatory-attempt-05.json"
I181T = OLD + "i181_six_cycle_helper/topology-attempt-01.json"
I180M = OLD + "i180_survivor_helper_connectivity/mandatory-attempt-02.json"
I180C = OLD + "i180_survivor_helper_connectivity/calibration-attempt-02.json"
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


def embed(full, local, row):
    table = dict(zip(local, row))
    return tuple(table.get(e, 0) for e in full)


def scaled_sum(pairs, n):
    total = (0,) * n
    for coefficient, row in pairs:
        total = vadd(total, vscale(coefficient, row))
    return total


def families_for(edges, uvxy):
    vertices = sorted({v for e in edges for v in e})
    u, v, x, y = uvxy
    e, f = edge(u, v), edge(x, y)
    cyc = cycles(vertices, edges)
    fam = {"N" + str(a) + str(b): [r for r in cyc
                                    if (r[edges.index(e)], r[edges.index(f)]) == (a, b)]
           for a, b in product(range(2), repeat=2)}
    ke = [h for h in edges if h not in (e, f)]
    for name, ends, pairing in [
            ("Pux", (u, x), (edge(u, x),)), ("Pvy", (v, y), (edge(v, y),)),
            ("D11", (u, v, x, y), tuple(sorted((edge(u, v), edge(x, y)))))]:
        rows = packings(vertices, ke, ends).get(pairing, [])
        fam[name] = [embed(edges, ke, r) for r in rows]
    return cyc, fam


def control(edges, uvxy, expected, retained=None):
    edges = sorted(map(tuple, edges))
    vertices = sorted({v for e in edges for v in e})
    u, v, x, y = uvxy
    e, f = edge(u, v), edge(x, y)
    cyc, fam = families_for(edges, uvxy)
    if retained is not None:
        for name, rows in retained.items():
            rows = sorted(vector(edges, r) if r and isinstance(r[0], list) else tuple(r)
                          for r in rows)
            eq(fam[name], rows, "complete family " + name)
    surv = sorted(fam["N10"] + fam["N01"] + fam["N11"])
    assert all(fam.values())
    L = diff_rows(surv)
    V = diff_rows(fam["N00"])
    L0 = sum((diff_rows(fam[k]) for k in ("N10", "N01", "N11")), [])
    U = sum((diff_rows(fam[k]) for k in ("Pux", "Pvy", "D11")), [])
    P, Q, D = (fam[k][0] for k in ("Pux", "Pvy", "D11"))
    A, B, C, N = (fam[k][0] for k in ("N10", "N01", "N11", "N00"))
    twice = tuple(2 if h in (e, f) else 0 for h in edges)
    b = vadd(P, Q, D, twice, vscale(-3, surv[0]))
    beta = vadd(P, Q, D, twice, vscale(-1, A), vscale(-1, B), vscale(-1, C))
    c = vadd(N, vscale(-1, A), vscale(-1, B), C)
    for name, row in (("b", b), ("beta", beta), ("c", c)):
        eq(row, expected[name], name)
        assert all(sum(row[j] for j, h in enumerate(edges) if vtx in h) == 0
                   for vtx in vertices)
    assert beta[edges.index(e)] == beta[edges.index(f)] == 0
    assert rank(L + [vsub(b, beta)]) == rank(L)
    assert rank([tuple(r[edges.index(h)] for h in (e, f)) for r in L]) == 2
    goodspace, residualspace, res = [], [], {}
    for name, ends in (("Pux", (u, x)), ("Pvy", (v, y)), ("D11", (u, v, x, y))):
        q = tuple(expected["residuals"][name]["q"])
        if name != "D11":
            support = [h for h, bit in zip(edges, q) if bit]
            sup_vertices = sorted({w for h in support for w in h})
            parts, adjacency = components(sup_vertices, support)
            assert len(parts) == 1
            assert sorted(w for w in sup_vertices if len(adjacency[w]) == 1) == sorted(ends)
            assert all(sum(q[j] for j, h in enumerate(edges) if w in h) ==
                       (1 if w in ends else 0) for w in vertices)
            assert all(bit in (-1, 0, 1) for bit in q)
        else:
            eq(q, vadd(res["Pux"]["q"], res["Pvy"]["q"]), "double arc")
        good = [r for r in fam["N00"] if vsub(r, q) in fam[name]]
        residual = [r for r in fam[name] if vadd(r, q) not in fam["N00"]]
        anchor = vsub(good[0], q) if good else fam[name][0]
        directions = [vsub(r, anchor) for r in (residual if good else fam[name])]
        res[name] = {"q": q, "good": good, "residual": residual,
                     "anchor": anchor, "residual_directions": directions}
        eq(res[name], expected["residuals"][name], "residual " + name)
        goodspace += diff_rows(good)
        residualspace += directions
        assert rank(diff_rows(fam[name])) == rank(diff_rows(good) + directions)
    assert rank(U + goodspace + residualspace) == rank(U) == rank(goodspace + residualspace)
    rL, rLU = rank(L), rank(L + U)
    ell = rank(diff_rows(cyc)) - rL
    t = rLU - rL
    eta = rank(L + U + [b]) - rLU
    delta_V = rank(L0 + V) - rank(L0 + goodspace)
    delta_R = rank(L0 + goodspace + residualspace) - rank(L0 + goodspace)
    epsilon = rank(L0 + V + [c]) - rank(L0 + V)
    assert ell - t == delta_V + epsilon - delta_R
    assert rL == 2 + rank(L0) and rLU == 2 + rank(L0 + U)
    row = {"counts": {k: len(vv) for k, vv in fam.items()},
           "arcs": [sum(bool(x) for x in res[k]["q"]) for k in ("Pux", "Pvy")],
           "dg": rank(diff_rows(cyc)), "rankL": rL, "rankL0": rank(L0),
           "rankU": rank(U), "rankUV": rank(U + V), "ell": ell, "t": t, "eta": eta,
           "delta_V": delta_V, "delta_R": delta_R, "epsilon": epsilon}
    eq(row, expected["row"], "control ranks")
    for name, result in (("V_subset_U", rank(U + V) == rank(U)),
                         ("V_subset_LU", rank(L + U + V) == rLU)):
        if name in expected:
            assert result == expected[name], name
    return {"row": row, "b": b, "beta": beta, "c": c, "residuals": res,
            "families": fam, "cycles": cyc}


def step_vertices(graph, step):
    face = graph["faces"][step[0]]
    i, j = step[1:]
    return [face[i], face[(i + 1) % len(face)], face[(j + 1) % len(face)], face[j]]


def k6(expected, uniform):
    k, n, j = 6, 5, 3
    T = lambda i: 12 + i
    B = lambda i: 18 + i

    def tr(a, b):
        step = 1 if b >= a else -1
        return [T(i) for i in range(a, b + step, step)]

    def br(a, b):
        step = 1 if b >= a else -1
        return [B(i) for i in range(a, b + step, step)]
    p, q, s, t = 26, 27, 24, 25
    W = [T(1), B(1), B(2), T(2), T(3), B(3)]
    V = [T(1), T(2), B(2), B(3), T(3)]
    words = {
        "0": [tr(1, j) + [p, q] + tr(n - 1, n) + br(n, 0)],
        "1a": [[B(0), B(1)] + V + [p, q, T(n - 1), B(n - 1), B(n), T(n)]],
        "1b": [[T(n), T(n - 1), q, p] + tr(j, 1) + br(1, n) + [B(0)]],
        "2": [[T(n), T(n - 1), B(n - 1), B(n), B(0), B(1)] + V + [p, q]],
        "3": [[B(0), B(n), T(n), T(n - 1)] + br(n - 1, 1) + tr(1, j) + [p, q]],
        "4a": [W + [B(n - 1), B(n), B(0)], [T(n), T(n - 1), q, p]],
        "4b": [tr(1, j) + br(j, 0), [T(n), B(n), B(n - 1), T(n - 1), q, p]],
        "5": [W + [B(n - 1), T(n - 1), q, p], [T(n), B(n), B(0)]],
        "6(n-1)": [tr(1, j) + [p], [T(n), B(n)] + br(0, n - 1) + [T(n - 1), q]],
        "7Z": [W + [B(n - 1), T(n - 1), T(n), B(n), B(0)], [p, q]],
        "8": [tr(1, j) + [p], br(0, n) + [T(n), T(n - 1), q]],
        "9": [[T(n), B(n), B(0)], [p] + tr(j, 1) + br(1, n - 1) + [T(n - 1), q]],
        "10a": [[T(n), B(n), B(n - 1), T(n - 1), q], [B(0), B(1)] + V + [p]],
        "10b": [[T(n), T(n - 1), q], [B(0)] + br(n, 1) + tr(1, j) + [p]],
    }
    for r in range(1, j):
        words["6r" + str(r)] = [tr(1, r) + br(r, 0) + br(n, r + 1) + tr(r + 1, j) + [p],
                                [T(n), T(n - 1), q]]
        words["7r" + str(r)] = [tr(1, r) + br(r, 0),
                                [p] + tr(j, r + 1) + br(r + 1, n) + [T(n), T(n - 1), q]]
    eq(words, expected["words"], "U176 words")
    xe = sorted([edge(T(i), B(i)) for i in range(1, n + 1)] +
                [edge(T(i), T(i + 1)) for i in range(1, n) if i != j] +
                [edge(B(i), B((i + 1) % (n + 1))) for i in range(n + 1)] +
                [edge(T(j), p), edge(p, q), edge(q, T(n - 1))])
    ye = [(1, 7), (1, s), (2, 3), (2, 8), (2, t), (3, 4), (3, 9),
          (4, 5), (4, 10), (5, 11), (6, 7), (6, 11), (7, 8), (8, 9),
          (9, 10), (10, 11), (s, t)]
    cut = [(1, T(1)), (5, T(n)), (6, B(0)), (s, p), (t, q)]
    es = sorted(xe + ye + cut)
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
        eq(sorted(edge(ports.index(path[0]), ports.index(path[-1])) for path in paths),
           TYPES[state][1])
    selected = ["0", "1a", "2", "3", "4a", "5", "6r1", "7Z", "8", "9", "10a"]
    anchors = []
    for i, name in enumerate(selected):
        y = tuple(uniform["anchors"][i]["Y"])
        used = TYPES[i][0]
        row = vadd(embed(es, xe, local[name]), embed(es, ye, y),
                   vector(es, [cut[m] for m in used]))
        sig = signature(sorted({v for e in es for v in e}), es, row)
        assert len(sig["cycles"]) == 1 and not sig["pairing"]
        assert row[es.index(cut[2])] or row[es.index((1, 7))]
        eq(row, uniform["anchors"][i]["cycle"])
        anchors.append(row)
    eq(anchors, expected["anchors"])
    dirs = [vsub(local["6r" + str(r)], local["6(n-1)"]) for r in (1, 2)]
    dirs += [vsub(local[a], local[b]) for a, b in
             (("1a", "1b"), ("4a", "4b"), ("7Z", "7r1"))]
    cols = [(13, 14), (14, 15), (16, 17), (26, 27), (18, 19)]
    minor = [[row[xe.index(e)] for e in cols] for row in dirs]
    eq(minor, expected["local_minor"])
    assert determinant(minor) == -2
    states = uniform["states"]
    images = [embed(es, ye, vsub(states[1]["Y"][1], states[1]["Y"][0]))]
    images += [embed(es, ye, vsub(states[4]["Y"][i], states[4]["Y"][0])) for i in (1, 2)]
    images += [vsub(anchors[i], anchors[0]) for i in (1, 2, 3, 4, 5, 7)]
    image_cols = [(1, 7), (1, s), (2, 3), (2, 8), (3, 4), (4, 5), (5, 11), (6, 7), (s, t)]
    image_minor = [[r[es.index(e)] for e in image_cols] for r in images]
    assert determinant(image_minor) == 1
    eq(image_minor, [[int(x) for x in r] for r in expected["image_minor"]])
    return {"words": words, "anchors": anchors,
            "local_minor": minor, "image_minor": image_minor}


def presentation(data):
    es = sorted(map(tuple, data["edges"]))
    xe = sorted(map(tuple, data["xe"]))
    ye = sorted(map(tuple, data["ye"]))
    cut = [tuple(e) for e in data["cut"]]
    X, Y, xp = list(data["X"]), list(data["Y"]), list(data["xp"])
    yp = [next(v for v in e if v in Y) for e in cut]
    complete = []
    all_products, survivors = set(), set()
    states = {}
    for size in (2, 4):
        for J in combinations(range(5), size):
            sides = []
            for verts, ee, ports in ((X, xe, xp), (Y, ye, yp)):
                fam = packings(verts, ee, [ports[m] for m in J])
                relabelled = {tuple(sorted(edge(ports.index(a), ports.index(b))
                                           for a, b in pairing)): rows
                              for pairing, rows in fam.items()}
                sides.append(relabelled)
            lx, ly = sides
            complete.append({"J": J,
                             "local": [{"pairing": pr, "packings": rr}
                                       for pr, rr in sorted(lx.items())],
                             "exterior": [{"pairing": pr, "packings": rr}
                                          for pr, rr in sorted(ly.items())]})
            for px, xrows in lx.items():
                for py, yrows in ly.items():
                    if size == 4 and px == py:
                        continue
                    for a_row, b_row in product(xrows, yrows):
                        row = vadd(embed(es, xe, a_row), embed(es, ye, b_row),
                                   vector(es, [cut[m] for m in J]))
                        sig = signature(X + Y, es, row)
                        assert len(sig["cycles"]) == 1
                        all_products.add(row)
                        if 2 in J or b_row[ye.index((1, 7))]:
                            survivors.add(row)
                            key = (J, px)
                            state = states.setdefault(key, {"X": set(), "Y": set(), "py": py})
                            assert state["py"] == py
                            state["X"].add(a_row)
                            state["Y"].add(b_row)
    eq(complete, data["complete"], "all complete fibres including empties")
    assert len(all_products) == data["full"] == 64
    assert len(survivors) == data["survivors"] == 46
    assert set(states) == set(TYPES)
    xs, ys, anchors = [], [], []
    for i, key in enumerate(TYPES):
        state = states[key]
        a_list, b_list = sorted(state["X"]), sorted(state["Y"])
        eq(a_list, data["states"][i]["X"])
        eq(b_list, data["states"][i]["Y"])
        xs.append(a_list)
        ys.append(b_list)
        anchors.append(vadd(embed(es, xe, a_list[0]), embed(es, ye, b_list[0]),
                            vector(es, [cut[m] for m in key[0]])))
    A = [vsub(c, anchors[0]) for c in anchors]
    eq(A, data["A"])
    wx = sum(([embed(es, xe, r) for r in diff_rows(a_list)] for a_list in xs), [])
    wy = [embed(es, ye, vsub(ys[1][1], ys[1][0]))]
    wy += [embed(es, ye, vsub(ys[4][i], ys[4][0])) for i in (1, 2)]
    lifts = [vadd(A[6], A[1], vscale(-1, A[2]), vscale(-1, A[5])),
             vadd(A[8], A[1], vscale(-1, A[3]), vscale(-1, A[5])),
             vsub(A[9], vadd(A[1], A[7])),
             vadd(A[10], vscale(-1, A[1]), vscale(-1, A[4]), A[5], vscale(-1, A[7]))]
    eq(lifts, data["lifts"])
    pi = [es.index(e) for e in ye + cut]
    assert all(not r[m] for r in lifts for m in pi)
    image = wy + [A[i] for i in (1, 2, 3, 4, 5, 7)]
    assert rank([tuple(r[m] for m in pi) for r in image]) == 9
    assert rank(wx) == 5 and rank(wy) == 3 and rank(wx + lifts) == 7
    assert rank(wx + wy + A) == rank(diff_rows(sorted(survivors))) == 16
    residuals = []
    for co in data["completion"]:
        J = tuple(co["J"])
        target = vadd(xs[0][0], xs[2][0], vscale(-1, xs[3][0]),
                      vscale(4, xs[4][0]), vscale(-4, xs[5][0]))
        if len(J) == 4:
            target = vadd(target, vscale(-1, xs[0][0]), xs[7][0])
        eq(target, co["target"])
        lift = scaled_sum([(Fraction(a_), r) for a_, r in zip(co["coordinates"], image)],
                          len(es))
        relevant = next(c for c in complete if tuple(c["J"]) == J)
        pairing = ((0, 1),) if len(J) == 2 else ((0, 1), (3, 4))
        rows = next(c["packings"] for c in relevant["local"]
                    if tuple(c["pairing"]) == pairing)
        for x in rows:
            full = vadd(embed(es, xe, x), embed(es, ye, co["exterior"]),
                        vector(es, [cut[m] for m in J]))
            assert full in all_products and full not in survivors
            r = vsub(vsub(full, anchors[0]), lift)
            assert r == embed(es, xe, vsub(x, target))
            residuals.append(tuple(int(v) for v in r))
    eq(sorted(set(residuals)), sorted(set(map(tuple, data["residuals"]))))
    changes = 0
    for i in range(11):
        for alt in xs[i][1:]:
            assert rank(wx + [embed(es, xe, vsub(alt, xs[i][0]))]) == 5
            changes += 1
        for alt in ys[i][1:]:
            assert rank(wy + [embed(es, ye, vsub(alt, ys[i][0]))]) == 3
            changes += 1
    assert changes == 22
    return {"edges": es, "xe": xe, "X": X, "xp": xp, "xs": xs, "ys": ys,
            "A": A, "wx": wx, "wy": wy, "lifts": lifts, "image": image,
            "complete": complete, "residuals": sorted(set(residuals)),
            "anchor_changes": changes}


def overlay_components(edges, a, b):
    delta = [e for e, x, y in zip(edges, a, b) if x != y]
    verts = sorted({v for e in delta for v in e})
    groups, adjacency = components(verts, delta)
    out = []
    for group in groups:
        chosen = [e for e in delta if e[0] in group]
        out.append((chosen, all(len(adjacency[v]) == 2 for v in group)))
    return out


def toggle(edges, row, chosen):
    chosen = {tuple(e) for e in chosen}
    return tuple(1 - x if e in chosen else x for e, x in zip(edges, row))


def lock(pres, expected_p, expected_records):
    X, xe, xp = pres["X"], pres["xe"], pres["xp"]
    P = packings(X, xe, xp[:2])[(edge(xp[0], xp[1]),)]
    s = pres["xs"][0][0]
    eq(s, expected_p["state0"], "state0 path")
    eq(P, expected_p["P"], "lost fibre")
    masks = singles = failures = 0
    records = []
    for i, p in enumerate(P):
        parts = overlay_components(xe, p, s)
        good = []
        for mask in range(1 << len(parts)):
            selected = sum((part[0] for j, part in enumerate(parts) if mask >> j & 1), [])
            a_new = toggle(xe, p, selected)
            b_new = toggle(xe, s, selected)
            sig_a, sig_b = signature(X, xe, a_new), signature(X, xe, b_new)
            assert vadd(a_new, b_new) == vadd(p, s)
            valid = not (sig_a["cycles"] or sig_b["cycles"] or
                         sig_a["singletons"] or sig_b["singletons"])
            if valid:
                assert {a_new, b_new} == {p, s}
                good.append(mask)
            if mask.bit_count() == 1:
                singles += 1
                failures += not valid
            masks += 1
        records.append({"p": i, "components": [c for c, _ in parts], "valid_masks": good})
    assert (masks, singles, failures) == (18, 9, 8)
    result = {"masks": masks, "single_switches": singles,
              "cycle_failures": failures, "records": records}
    eq(result, expected_records, "I179 lock")
    return P, result


def helpers(pres, P, parent_expected, calibration, retained):
    xe, X = pres["xe"], pres["X"]
    identities = []
    for j, q in enumerate(P[1:], 1):
        for i, family in enumerate(pres["xs"]):
            for ui, u in enumerate(family):
                target = vsub(vadd(P[0], u), q)
                if target in family:
                    chosen = [e for e, a, b in zip(xe, P[0], q) if a != b]
                    parts = overlay_components(xe, P[0], u)
                    whole = any(iscycle and set(es_) == set(chosen)
                                for es_, iscycle in parts)
                    identities.append({"P_index": j, "state": i, "u_index": ui,
                                       "up_index": family.index(target),
                                       "changed_edges": chosen,
                                       "single_alternating_cycle": whole})
    eq(identities, parent_expected["solutions"], "parent exact identities")
    eq(identities, retained["parent_identities"], "retained parent identities")
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
                    q_new, v_new = toggle(xe, p, ce), toggle(xe, u, ce)
                    assert vadd(p, u) == vadd(q_new, v_new)
                    sig_q, sig_v = signature(X, xe, q_new), signature(X, xe, v_new)
                    valid = q_new in P and v_new in family
                    item = {"p_index": pi, "state": state, "u_index": ui, "cycle_edges": ce}
                    if valid:
                        graph.add(tuple(sorted((pi, P.index(q_new)))))
                        item.update(q_index=P.index(q_new), v_index=family.index(v_new))
                        witnesses.append(item)
                    else:
                        assert sig_q["cycles"], "Every retained failure is lost-output cyclic"
                        item.update(q=sig_q, v=sig_v)
                        rejected.append(item)
    assert (overlays, moves, len(witnesses), len(rejected)) == (130, 123, 24, 99)
    assert graph == {(0, 1), (1, 2), (2, 3), (3, 4)}
    for item in witnesses:
        assert any(all(json.loads(json.dumps(old[k])) == json.loads(json.dumps(v))
                       for k, v in item.items())
                   for old in calibration["witnesses"])
    exact = []
    for pi, qi in combinations(range(5), 2):
        for state, family in enumerate(pres["xs"]):
            for ui, vi in product(range(len(family)), repeat=2):
                if vadd(P[pi], family[ui]) != vadd(P[qi], family[vi]):
                    continue
                ce = [e for e, a, b in zip(xe, P[pi], P[qi]) if a != b]
                if any(iscycle and set(part) == set(ce)
                       for part, iscycle in overlay_components(xe, P[pi], family[ui])):
                    exact.append((pi, qi, state, ui, vi))
    assert len(exact) == 12
    assert sorted(exact) == sorted((w["p_index"], w["q_index"], w["state"],
                                    w["u_index"], w["v_index"])
                                   for w in witnesses if w["p_index"] < w["q_index"])
    for old in identities:
        if not old["single_alternating_cycle"]:
            assert not any(w["p_index"] == 0 and w["state"] == old["state"] and
                           w["u_index"] == old["u_index"] for w in witnesses)
    distances = [sum(a != b for a, b in zip(p, P[4])) for p in P]
    assert distances == [8, 8, 8, 6, 0]
    wx = sum((diff_rows(family) for family in pres["xs"]), [])
    ranks = [rank(diff_rows(P)), rank(wx), rank(wx + diff_rows(P))]
    assert ranks == [4, 5, 5]
    result = {"parent_identities": identities, "overlays": overlays, "cycle_moves": moves,
              "witnesses": witnesses, "rejected": rejected, "graph": sorted(graph),
              "exact_forward": exact, "distances": distances, "ranks": ranks}
    eq(result, retained, "I180 helper graph")
    return result


def perfect_pairings(items):
    if not items:
        yield []
        return
    first = items[0]
    for i in range(1, len(items)):
        for rest in perfect_pairings(items[1:i] + items[i + 1:]):
            yield [(first, items[i])] + rest


def patch_reattachment(retained):
    """Fresh I181 patch forcing and reattachment audit on the abstract patch."""
    boundary = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]
    chord = (0, 3)
    continuations = [(1, 6), (2, 7), (4, 8), (5, 9)]
    local_edges = sorted(boundary + [chord] + continuations)
    half_A = [(0, 1), (2, 3), (4, 5)]
    half_B = [(1, 2), (3, 4), (0, 5)]
    solutions = []
    for mask in range(1 << len(local_edges)):
        chosen = [e for i, e in enumerate(local_edges) if mask >> i & 1]
        if all(sum(1 for e in chosen if v in e) == 2 for v in range(6)):
            solutions.append(chosen)
    solved = {}
    for half, name in ((half_A, "A"), (half_B, "B")):
        match = [s for s in solutions
                 if set(map(tuple, s)) & set(map(tuple, boundary)) ==
                 set(map(tuple, half))]
        assert len(match) == 1, "exactly one degree-correct local set per exact half"
        solved[name] = match[0]
    for name, half in (("A", half_A), ("B", half_B)):
        sol = set(map(tuple, solved[name]))
        assert sol == set(map(tuple, half)) | {chord} | set(continuations), name
        sig = signature(list(range(10)), sorted(sol), (1,) * len(sol))
        assert not sig["cycles"], name
        assert sig["pairing"] == [(6, 7), (8, 9)], name
    vertices6 = list(range(6))
    sig_a = signature(vertices6, sorted(set(map(tuple, half_A)) | {chord}),
                      (1,) * 4)
    sig_b = signature(vertices6, sorted(set(map(tuple, half_B)) | {chord}),
                      (1,) * 4)
    route_a = sorted(sig_a["words"], key=lambda w: w[0])
    route_b = sorted(sig_b["words"], key=lambda w: w[0])
    eq(route_a, retained["routing_A"], "routing A")
    eq(route_b, retained["routing_B"], "routing B")
    rows = []
    for ports in ([6, 7], [6, 7, 8, 9]):
        nodes = [1, 2, 4, 5] + ports
        for segments in perfect_pairings(nodes):
            quotient = segments + [(1, 2), (4, 5)]
            groups, adjacency = components(nodes, quotient)
            cyclic = [g for g in groups if all(len(adjacency[v]) == 2 for v in g)]
            pairing = sorted(tuple(sorted(v for v in g if v in ports))
                             for g in groups if any(v in ports for v in g))
            reattachments = []
            for half in (half_A, half_B):
                edges = segments + half + [chord]
                gs, aa = components([0, 3] + nodes, edges)
                cyc = sum(all(len(aa[v]) == 2 for v in g) for g in gs)
                pp = sorted(tuple(sorted(v for v in g if v in ports))
                            for g in gs if any(v in ports for v in g))
                assert cyc == len(cyclic) and pp == pairing
                reattachments.append({"cycles": cyc, "pairing": pp})
            rows.append({"ports": ports, "segments": segments,
                         "quotient_cycles": len(cyclic), "pairing": pairing,
                         "reattachments": reattachments})
    assert len(rows) == 120 == retained["rows_count"]
    eq(rows, retained["rows"], "reattachment table")
    for es_ in [[(1, 1)], [(1, 2), (1, 2)]]:
        vs = sorted({v for e in es_ for v in e})
        gs, aa = components(vs, es_)
        assert len(gs) == 1 and all(len(aa[v]) == 2 for v in vs)
    return {"degree_correct_subsets": len(solutions),
            "half_containing_solutions": 2, "rows": rows, "rows_count": len(rows),
            "routing_A": route_a, "routing_B": route_b,
            "terminal_pairing": [[6, 7], [8, 9]]}


def mandatory():
    old_new = read_json(I181M)
    old_prev = read_json(I180M)
    for key in ("C171", "first_P8", "I176_k6", "I177", "I177_initial",
                "I177_absorption"):
        shared = set(old_new[key]) & set(old_prev[key])
        assert shared, key
        for field in shared:
            if field in ("graph", "cycles", "families", "matching_extensions"):
                continue
            if key == "I176_k6" and field == "image_minor":
                coerced = [[int(Fraction(x)) for x in row]
                           for row in old_prev[key][field]]
                eq(old_new[key][field], coerced, "cross-retained I176_k6 image_minor")
                continue
            eq(old_new[key][field], old_prev[key][field], "cross-retained " + key)
    for k in range(12):
        for field in ("row", "b", "beta", "c", "residuals"):
            eq(old_new["controls"][k][field], old_prev["controls"][k][field],
               "cross-retained control")
    for k in range(2):
        for field in ("row", "b", "beta", "c", "residuals", "nonbrace_pair"):
            eq(old_new["G6_G10"][k][field], old_prev["G6_G10"][k][field],
               "cross-retained G6/G10")
    out = {"order": [], "controls": []}
    source = read_json(OLD + "i169_bridge_independence/audit-attempt-02.json")["rows"]
    for index, expected, retained_new in zip(ORDER, old_prev["controls"],
                                             old_new["controls"]):
        data = source[index]
        assert data["index"] == expected["index"] == index
        result = control(data["parent_edges"], data["labels"][:4], expected,
                         data["classes"])
        for field in ("row", "b", "beta", "c", "residuals"):
            eq(result[field], retained_new[field], "retained control field")
        out["controls"].append(result)
        out["order"].append(index)
    c171 = read_json(OLD + "i172_prescribed_square_switch/mandatory-attempt-01.json")["C171"]
    es = sorted(map(tuple, c171["graph"]["edges"]))
    uvxy = step_vertices(c171["graph"], c171["row"]["step"])
    result = control(es, uvxy, old_prev["C171"])
    for field in ("row", "b", "beta", "c", "residuals"):
        eq(result[field], old_new["C171"][field], "retained C171")
    result["graph"] = graph_check(c171["graph"], c171["extensions"])
    w, C0, F, T = (list(map(Fraction, c171[k])) for k in ("w", "C0", "F", "T"))
    assert F != T
    for r, value in ((F, Fraction(1, 14)), (T, Fraction(-1, 2))):
        assert sum(a * b for a, b in zip(w, vsub(r, C0))) == value
        assert len(signature(sorted({v for e in es for v in e}), es, r)["cycles"]) == 2
    pre = tuple(old_prev["C171"]["switch"]["precycle"])
    square = [tuple(e) for e in old_prev["C171"]["switch"]["square"]]
    assert toggle(es, pre, square) == tuple(F) and pre in result["cycles"]
    out["C171"] = result
    out["order"].append("C171")
    records = read_json(OLD + "i172_prescribed_square_switch/cut-octagons-attempt-01.json")["records"]
    out["G6_G10"] = []
    for size, expected, retained_new in zip((6, 10), old_prev["G6_G10"],
                                            old_new["G6_G10"]):
        data = next(a for a in records if a["L"] == size)
        z = control(data["graph"]["edges"],
                    step_vertices(data["graph"], data["row"]["step"]),
                    expected, data["families"])
        es_g = sorted(map(tuple, data["graph"]["edges"]))
        vs = sorted({v for e in es_g for v in e})
        matchings = degree_solutions(vs, es_g, {v: 1 for v in vs})
        pair = list(map(tuple, expected["nonbrace_pair"]))
        assert not any(all(r[es_g.index(e)] for e in pair) for r in matchings)
        z["nonbrace_pair"] = pair
        z["perfect_matchings"] = len(matchings)
        for field in ("row", "b", "beta", "c", "residuals", "nonbrace_pair",
                      "perfect_matchings"):
            eq(z[field], retained_new[field], "retained G6/G10")
        out["G6_G10"].append(z)
    out["order"].append("G6/G10")
    p8 = read_json(OLD + "i175_affected_prism_exterior/experiment-attempt-01.json")["first_children"][0]
    result = control(p8["graph"]["edges"], p8["uvxy"], old_prev["first_P8"],
                     p8["families"])
    result["graph"] = graph_check(p8["graph"], p8["brace"]["extensions"])
    for field in ("row", "b", "beta", "c", "residuals"):
        eq(result[field], old_new["first_P8"][field], "retained first P8")
    out["first_P8"] = result
    out["order"].append("first_P8")
    uniform = read_json(OLD + "i176_uniform_five_port_rank/uniform-attempt-02.json")["checks"][0]
    assert uniform["k"] == 6
    result = k6(old_prev["I176_k6"], uniform)
    eq(result, old_new["I176_k6"], "retained I176 k6")
    out["I176_k6"] = result
    out["order"].append("I176_k6")
    child = read_json(OLD + "i177_adjacent_port_surgery/experiment-attempt-03.json")
    data = child["child"]
    result = control(data["graph"]["edges"], data["uvxy"], old_prev["I177"],
                     data["families"])
    result["graph"] = graph_check(data["graph"], data["brace"]["extensions"])
    for field in ("row", "b", "beta", "c", "residuals"):
        eq(result[field], old_new["I177"][field], "retained I177")
    out["I177"] = result
    initial = child["initial"]
    result = control(initial["graph"]["edges"], initial["uvxy"],
                     old_prev["I177_initial"], initial["families"])
    for field in ("row", "b", "beta", "c", "residuals"):
        eq(result[field], old_new["I177_initial"][field], "retained I177 initial")
    out["I177_initial"] = result
    d = old_prev["I178"]
    es, xe, ye = (list(map(tuple, d[k])) for k in ("edges", "xe", "ye"))
    es = sorted(es)
    xe, ye = sorted(xe), sorted(ye)
    xs = [list(map(tuple, s["X"])) for s in d["states"]]
    A = list(map(tuple, d["A"]))
    Xb = [embed(es, xe, vsub(xs[1][1], xs[1][0]))]
    Xb += [embed(es, xe, vsub(xs[5][i], xs[5][0])) for i in range(1, 5)]
    Yb = list(map(tuple, d["Ybasis"]))
    lifts = list(map(tuple, d["lifts"]))
    base = Xb + Yb + [A[i] for i in (1, 2, 3, 4, 5, 7)] + lifts[:2]
    assert rank(base) == 16
    old_es = sorted(map(tuple, initial["graph"]["edges"]))

    def tau(r):
        row = list(embed(es, old_es, r))
        a_val = r[old_es.index((1, 2))]
        b_val = r[old_es.index((13, 14))]
        for e, x in [((1, 28), a_val), ((2, 29), a_val), ((13, 30), b_val),
                     ((14, 31), b_val), ((28, 29), -a_val), ((30, 31), -b_val),
                     ((28, 30), 0), ((29, 31), 0)]:
            row[es.index(e)] = x
        return tuple(row)
    for equation in old_prev["I177_absorption"]["equations"]:
        target = tau(equation["old_direction"])
        eq(target, equation["transport"])
        assert target == scaled_sum(
            [(Fraction(c_), b_) for c_, b_ in zip(equation["coefficients"], base)],
            len(es))
    old_diff = diff_rows(out["I177_initial"]["cycles"])
    assert rank([tau(r) for r in old_diff]) == rank(old_diff) == 14
    rhs = vadd(vscale(5, Xb[0]), *[vscale(-1, r) for r in Xb[1:]],
               lifts[0], vscale(2, lifts[1]))
    assert vscale(3, lifts[2]) == vscale(3, lifts[3]) == rhs
    cols = child["actual_survivor_minor"]["columns"]
    for r in data["survivor_basis"]:
        assert vadd(r, data["survivor_anchor"]) in out["I177"]["cycles"]
    assert determinant([[r[i] for i in cols] for r in data["survivor_basis"]]) == 2
    out["I177_absorption"] = old_prev["I177_absorption"]
    out["order"].append("I177_child_absorption")
    pres = presentation(d)
    section = {k: v for k, v in pres.items() if k not in ("xs", "ys")}
    eq(section, old_new["I178"], "retained I178")
    out["I178"] = section
    out["order"].append("I178_relations_completion")
    P, out["I179_lock"] = lock(pres, old_prev["I179_lock"], old_new["I179_lock"])
    out["order"].append("I179_lock")
    cal = read_json(I180C)
    out["helper"] = helpers(pres, P, old_prev["parent_helper"], cal,
                            old_new["helper"])
    out["order"] += ["parent_helper", "I180_helpergraph"]
    topo = read_json(I181T)
    out["I181_patch_reattachment"] = patch_reattachment(topo)
    out["order"].append("I181_patch_reattachment")
    out["status"] = "PASS"
    return out


def label_pairing(pairing, xp):
    labels = []
    for a, b in pairing:
        labels.append(edge(xp.index(a), xp.index(b)))
    return tuple(sorted(labels))


def relabelled_fibres(vertices, edges, ports, used):
    fam = packings(vertices, edges, [ports[m] for m in used])
    return {tuple(sorted(edge(ports.index(a), ports.index(b)) for a, b in pr)): rows
            for pr, rows in fam.items()}


def extension():
    """E182 diagnostic on the retained authenticated glued graph.

    Enumerates the two-square patches of the retained graph, the lost
    alternating-half instances on them, and every perfect matching of the
    vertex-deleted graph; classifies each complement. No new graph is built.
    """
    child = read_json(OLD + "i177_adjacent_port_surgery/experiment-attempt-03.json")["child"]
    es = sorted(map(tuple, child["graph"]["edges"]))
    faces = [list(f) for f in child["graph"]["faces"]]
    vertices = sorted({v for e in es for v in e})
    d = read_json(I180M)["I178"]
    xe = sorted(map(tuple, d["xe"]))
    ye = sorted(map(tuple, d["ye"]))
    cut = [tuple(e) for e in d["cut"]]
    X, Y, xp = list(d["X"]), list(d["Y"]), list(d["xp"])
    yp = [next(v for v in e if v in Y) for e in cut]
    assert es == sorted(xe + ye + cut)
    graph_status = graph_check(child["graph"], child["brace"]["extensions"])
    P = packings(X, xe, xp[:2])[(edge(xp[0], xp[1]),)]
    cal = read_json(I180C)
    eq(P, sorted(tuple(r["vector"]) for r in cal["P"]), "retained lost fibre")
    survivor_fibres = []
    for used, pairing in TYPES:
        wanted = tuple(sorted(tuple(map(tuple, pairing))))
        survivor_fibres.append(
            relabelled_fibres(X, xe, xp, used).get(wanted, []))
    exterior_all = [relabelled_fibres(Y, ye, yp, used) for used, _ in TYPES]
    ports = set(xp)
    quads = [f for f in faces if len(f) == 4]
    patches = []
    excluded = []
    for f1, f2 in combinations(quads, 2):
        e1 = {edge(f1[i], f1[(i + 1) % 4]) for i in range(4)}
        e2 = {edge(f2[i], f2[(i + 1) % 4]) for i in range(4)}
        shared = e1 & e2
        if len(shared) != 1:
            continue
        boundary = sorted(e1 ^ e2)
        bverts = sorted({v for e in boundary for v in e})
        groups, adjacency = components(bverts, boundary)
        simple = (len(bverts) == 6 and len(groups) == 1 and
                  all(len(adjacency[v]) == 2 for v in bverts))
        if not simple:
            excluded.append({"faces": [f1, f2], "reason": "boundary not a simple six-cycle"})
            continue
        if not set(bverts) <= set(X):
            excluded.append({"faces": [f1, f2], "reason": "not internal to X"})
            continue
        if set(bverts) & ports:
            excluded.append({"faces": [f1, f2], "reason": "meets the five ports"})
            continue
        chord = next(iter(shared))
        patches.append({"faces": [f1, f2], "boundary": boundary, "chord": chord})
    instances = []
    reduction_checks = 0
    for patch in patches:
        boundary = patch["boundary"]
        chord = patch["chord"]
        x, y = chord
        bverts = sorted({v for e in boundary for v in e})
        _, badj = components(bverts, boundary)
        others = [v for v in bverts if v not in chord]
        continuation = {}
        for v in others:
            third = [e for e in es if v in e and e not in boundary]
            assert len(third) == 1
            continuation[v] = third[0]
        for pi, qi in combinations(range(len(P)), 2):
            for p_row, q_row, forward in ((P[pi], P[qi], True),
                                          (P[qi], P[pi], False)):
                diff = [e for e, a, b in zip(xe, p_row, q_row) if a != b]
                if set(diff) != set(boundary):
                    continue
                half_used = sorted(e for e in boundary
                                   if p_row[xe.index(e)])
                assert len(half_used) == 3
                a_v = next(v for v in others if edge(x, v) in half_used)
                c_v = next(v for v in others if edge(x, v) not in half_used)
                b_v = next(v for v in others
                           if v != a_v and edge(v, y) in half_used)
                d_v = next(v for v in others if v not in (a_v, b_v, c_v))
                assert edge(a_v, b_v) in boundary and edge(a_v, b_v) not in half_used
                assert edge(c_v, d_v) in boundary and edge(c_v, d_v) in half_used
                assert edge(d_v, y) in boundary and edge(d_v, y) not in half_used
                assert edge(x, c_v) in boundary and edge(x, c_v) not in half_used
                half_other = sorted(set(boundary) - set(half_used))
                t_ends = {k: next(w for w in continuation[v] if w != v)
                          for k, v in (("a", a_v), ("b", b_v),
                                       ("c", c_v), ("d", d_v))}
                g_verts = [v for v in vertices if v not in bverts]
                g_edges = [e for e in es if not (set(e) & set(bverts))]
                matchings = degree_solutions(g_verts, g_edges, {v: 1 for v in g_verts})
                summary = {"total": len(matchings), "hamiltonian": 0,
                           "controlled": 0, "lost_P": 0, "lost_D": 0,
                           "parallel_pairing": 0, "with_closed_components": 0}
                fibres_hit = {}
                witness = {}
                controlled_rows = set()
                for m_row in matchings:
                    full_m = dict(zip(g_edges, m_row))
                    m_bits = tuple(1 if e in half_used else full_m.get(e, 0) for e in es)
                    assert sum(m_bits) == len(vertices) // 2
                    h_bits = tuple(1 - b for b in m_bits)
                    h_edges = [e for e, b in zip(es, h_bits) if b]
                    h_groups, h_adj = components(vertices, h_edges)
                    assert all(len(h_adj[v]) == 2 for v in vertices)
                    hamiltonian = len(h_groups) == 1
                    hp_edges = [e for e in g_edges
                                if not m_row[g_edges.index(e)]]
                    hp_groups, hp_adj = components(g_verts, hp_edges)
                    deg1 = sorted(v for v in g_verts if len(hp_adj[v]) == 1)
                    assert deg1 == sorted(t_ends.values())
                    closed = [g for g in hp_groups
                              if all(len(hp_adj[v]) == 2 for v in g)]
                    path_pairs = sorted(
                        tuple(sorted(v for v in g if len(hp_adj[v]) == 1))
                        for g in hp_groups
                        if any(len(hp_adj[v]) == 1 for v in g))
                    parallel = (path_pairs == sorted([
                        tuple(sorted((t_ends["a"], t_ends["b"]))),
                        tuple(sorted((t_ends["c"], t_ends["d"])))]))
                    cross = not closed and len(path_pairs) == 2 and not parallel
                    assert hamiltonian == cross
                    reduction_checks += 1
                    if closed:
                        summary["with_closed_components"] += 1
                    if parallel and not closed:
                        summary["parallel_pairing"] += 1
                    if not hamiltonian:
                        continue
                    summary["hamiltonian"] += 1
                    local = tuple(h_bits[es.index(e)] for e in xe)
                    sig = signature(X, xe, local)
                    used = tuple(j for j, e in enumerate(cut) if h_bits[es.index(e)])
                    pairing = label_pairing(sig["pairing"], xp)
                    type_index = next((i for i, (uu, pp) in enumerate(TYPES)
                                       if tuple(uu) == used and
                                       tuple(map(tuple, pp)) == pairing), None)
                    if type_index is None:
                        assert (used, pairing) == ((0, 1), ((0, 1),)) or \
                               (used, pairing) == ((0, 1, 3, 4), ((0, 1), (3, 4)))
                        summary["lost_P" if used == (0, 1) else "lost_D"] += 1
                        continue
                    summary["controlled"] += 1
                    fibres_hit[type_index] = fibres_hit.get(type_index, 0) + 1
                    controlled_rows.add(m_bits)
                    witness.setdefault(type_index, [list(e) for e, b in
                                                    zip(es, m_bits) if b])
                    u_row = local
                    v_row = toggle(xe, u_row, boundary)
                    assert vadd(p_row, u_row) == vadd(q_row, v_row)
                helpers_confirmed = 0
                helpers_total = 0
                products_cyclic = 0
                half_other_set = set(map(tuple, half_other))
                half_used_set = set(map(tuple, half_used))
                for state, family in enumerate(survivor_fibres):
                    used, pairing = TYPES[state]
                    for u_row in family:
                        on_cycle = {e for e, bit in zip(xe, u_row) if bit}
                        if not half_other_set <= on_cycle:
                            continue
                        if on_cycle & half_used_set:
                            continue
                        helpers_total += 1
                        v_row = toggle(xe, u_row, boundary)
                        assert vadd(p_row, u_row) == vadd(q_row, v_row)
                        for py_label, yrows in exterior_all[state].items():
                            for y_row in yrows:
                                h_row = vadd(embed(es, xe, u_row),
                                             embed(es, ye, y_row),
                                             vector(es, [cut[m] for m in used]))
                                sig = signature(vertices, es, h_row)
                                single = len(sig["cycles"]) == 1 and not sig["pairing"]
                                assert single == (len(used) == 2 or
                                                  py_label != tuple(
                                                      sorted(tuple(map(tuple, pairing))))), \
                                    "complete product classification"
                                if not single:
                                    products_cyclic += 1
                                    continue
                                m_bits = tuple(1 - b for b in h_row)
                                assert m_bits in controlled_rows
                                helpers_confirmed += 1
                instances.append({
                    "patch_boundary": boundary, "chord": list(chord),
                    "p_index": pi if forward else qi,
                    "q_index": qi if forward else pi,
                    "half_A": [list(e) for e in half_used],
                    "half_B": [list(e) for e in half_other],
                    "continuation_edges": sorted(list(map(list, continuation.values()))),
                    "terminal_vertices": t_ends,
                    "matchings": summary,
                    "fibres_hit": fibres_hit,
                    "witness_matchings": witness,
                    "helpers_total": helpers_total,
                    "helpers_confirmed": helpers_confirmed,
                    "products_cyclic": products_cyclic,
                })
    return {"status": "PASS",
            "scope": "Retained glued graph only; no new graph tests",
            "graph": graph_status,
            "patches_internal": len(patches),
            "patches_excluded": excluded,
            "instances": instances,
            "instances_count": len(instances),
            "all_instances_controlled": bool(instances) and all(
                i["matchings"]["controlled"] > 0 for i in instances),
            "reduction_checks": reduction_checks,
            "E182": "UNRESOLVED"}
