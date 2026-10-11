"""Targeted controls first, followed by the sole authorized calibration."""
from math180 import *

ORDER = [0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539, 431]
BASE = "frontier/experiments/"
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


def noncrossing(pairs):
    order = (0, 2, 1, 4, 3)
    intervals = [sorted(order.index(x) for x in pair) for pair in pairs]
    return all(not (a < c < b < d or c < a < d < b)
               for (a, b), (c, d) in combinations(intervals, 2))


def interface(graph, cut, xvertices, expected=None):
    vertices, edges, colors = graph_check(graph)
    X = sorted(xvertices)
    Y = sorted(set(vertices) - set(X))
    xe = [e for e in edges if set(e) <= set(X)]
    ye = [e for e in edges if set(e) <= set(Y)]
    cut = [tuple(e) for e in cut]
    assert set(edges) == set(xe + ye + cut)
    xp = [next(v for v in e if v in X) for e in cut]
    yp = [next(v for v in e if v in Y) for e in cut]
    assert len(set(xp)) == len(set(yp)) == 5 and len(Y) == 13
    assert len(components(adjacency(X, xe))) == 1
    assert [colors[v] for v in xp] == [1, 1, 1, 0, 1]
    assert all(len(ns) == (2 if v in xp else 3) for v, ns in adjacency(X, xe).items())
    turns = {}
    for face in graph["faces"]:
        for i, v in enumerate(face):
            turns[v, face[i - 1]] = face[(i + 1) % len(face)]
    successor = {}
    for i in range(5):
        prev, cur = yp[i], xp[i]
        visited = set()
        while True:
            assert (prev, cur) not in visited
            visited.add((prev, cur))
            nxt = turns[cur, prev]
            if nxt in Y:
                successor[i] = cut.index(edge(cur, nxt))
                break
            prev, cur = cur, nxt
    border = [0]
    while successor[border[-1]] != 0:
        border.append(successor[border[-1]])
        assert len(border) <= 5
    assert border == [0, 2, 1, 4, 3], border
    allx, ally, complete = {}, {}, []
    for count in (2, 4):
        for J in combinations(range(5), count):
            x = packings(X, xe, [xp[j] for j in J])
            y = packings(Y, ye, [yp[j] for j in J])
            xx = {tuple(sorted(edge(xp.index(a), xp.index(b)) for a, b in pairing)): fs
                  for pairing, fs in x.items()}
            yy = {tuple(sorted(edge(yp.index(a), yp.index(b)) for a, b in pairing)): fs
                  for pairing, fs in y.items()}
            assert all(noncrossing(p) for p in xx)
            for pairing, fs in x.items():
                if len(pairing) == 2:
                    assert fs == two_paths(X, xe, pairing)
            allx[J], ally[J] = xx, yy
            complete.append({"J": J,
                             "local": [{"pairing": p, "packings": fs} for p, fs in sorted(xx.items())],
                             "exterior": [{"pairing": p, "packings": fs} for p, fs in sorted(yy.items())]})

    def lift(v, side):
        return tuple(v[side.index(e)] if e in side else 0 for e in edges)

    def glue(a, b, J):
        return plus(lift(a, xe), lift(b, ye), tuple(int(e in [cut[j] for j in J]) for e in edges))

    states, full, survivors, lost = [], set(), set(), {}
    for J, xx in allx.items():
        for px, fs in sorted(xx.items()):
            partners = []
            badpartners = []
            for py, ys in sorted(ally[J].items()):
                if len(J) == 4 and px == py:
                    continue
                for b in ys:
                    for a in fs:
                        c = glue(a, b, J)
                        assert len(components(adjacency(vertices, edges, c))) == 1
                        full.add(c)
                    if 2 in J or b[ye.index((1, 7))]:
                        partners.append(b)
                    else:
                        badpartners.append(b)
            partners.sort()
            if partners:
                products = sorted(glue(a, b, J) for a in fs for b in partners)
                survivors.update(products)
                assert len(set(products)) == len(products)
                states.append({"J": J, "px": px, "X": fs, "Y": partners,
                               "anchor": glue(fs[0], partners[0], J), "products": products})
            if badpartners:
                lost[J, px] = (fs, sorted(badpartners))
    states.sort(key=lambda s: (len(s["J"]), s["J"], s["px"]))
    assert [(s["J"], s["px"]) for s in states] == TYPES
    assert len(full) == sum(len(s["products"]) for s in states) + sum(
        len(fs) * len(ys) for fs, ys in lost.values())
    cycles = hamiltonian(vertices, edges)
    assert sorted(full) == cycles
    assert sorted(survivors) == [c for c in cycles if c[edges.index(cut[2])] or c[edges.index((1, 7))]]
    localdirs = [lift(d, xe) for s in states for d in differences(s["X"])]
    exdirs = [lift(d, ye) for s in states for d in differences(s["Y"])]
    anchors = [s["anchor"] for s in states]
    A = [minus(c, anchors[0]) for c in anchors]
    Ybasis = [lift(minus(states[1]["Y"][1], states[1]["Y"][0]), ye)] + [
        lift(minus(states[4]["Y"][i], states[4]["Y"][0]), ye) for i in (1, 2)]
    assert rank(Ybasis) == rank(exdirs) == 3
    generators = Ybasis + A[1:]
    projection = [i for i, e in enumerate(edges) if e not in xe]
    projected = [tuple(v[i] for i in projection) for v in generators]
    assert rank(projected) == 9
    lifts = [plus(A[6], A[1], scale(-1, A[2]), scale(-1, A[5])),
             plus(A[8], A[1], scale(-1, A[3]), scale(-1, A[5])),
             plus(A[9], scale(-1, A[1]), scale(-1, A[7])),
             plus(A[10], scale(-1, A[1]), scale(-1, A[4]), A[5], scale(-1, A[7]))]
    assert all(all(v[i] == 0 for i in projection) for v in lifts)
    kernel = integer_basis(localdirs + lifts)
    assert rank(kernel) == rank(differences(sorted(survivors))) - 9
    imagebasis = Ybasis + [A[i] for i in (1, 2, 3, 4, 5, 7)]
    assert rank([tuple(v[i] for i in projection) for v in imagebasis]) == 9
    x = [s["X"][0] for s in states]
    targetP = plus(x[0], x[2], scale(-1, x[3]), scale(4, x[4]), scale(-4, x[5]))
    targetD = plus(x[2], scale(-1, x[3]), scale(4, x[4]), scale(-4, x[5]), x[7])
    assert set(lost) == {((0, 1), ((0, 1),)), ((0, 1, 3, 4), ((0, 1), (3, 4)))}
    completion, residuals = [], []
    for (J, px), (fs, partners) in sorted(lost.items()):
        target = targetP if len(J) == 2 else targetD
        assert len(partners) == 3
        for j, y in enumerate(partners):
            coords = [-3, 1 + int(j == 1), 1 + int(j == 2), 0, 1, -1, 4, -4, int(len(J) == 4)]
            image_lift = plus(*(scale(a, b) for a, b in zip(coords, imagebasis)))
            for p in fs:
                residual = minus(minus(glue(p, y, J), anchors[0]), image_lift)
                assert residual == lift(minus(p, target), xe)
                assert all(sum(residual[i] for i, e in enumerate(edges) if v in e) == 0 for v in X)
                residuals.append(residual)
            completion.append({"J": J, "exterior": y, "coordinates": coords, "target": target})
    assert rank(kernel + residuals) + 9 == rank(differences(cycles))
    # Recompute transformed relations, never re-use fixed coefficients after Y-anchor changes.
    anchor_changes = []
    for i, state in enumerate(states):
        for side in ("X", "Y"):
            for j in range(1, len(state[side])):
                aa = anchors[:]
                aa[i] = glue(state["X"][j] if side == "X" else state["X"][0],
                             state["Y"][j] if side == "Y" else state["Y"][0], state["J"])
                gg = Ybasis + [minus(c, aa[0]) for c in aa[1:]]
                rr = nullspace([[g[t] for g in gg] for t in projection], 13)
                kk = [plus(*(scale(a, b) for a, b in zip(r, gg))) for r in rr]
                assert len(rr) == 4 and equalspan(localdirs + kk, kernel)
                anchor_changes.append({"state": i, "side": side, "index": j,
                                       "relations": rr, "lifts": kk})
    aa = [glue(s["X"][-1], s["Y"][-1], s["J"]) for s in states]
    newY = [plus(Ybasis[0], Ybasis[1]), Ybasis[1], plus(Ybasis[1], Ybasis[2])]
    gg = newY + [minus(c, aa[0]) for c in aa[1:]]
    rr = nullspace([[g[t] for g in gg] for t in projection], 13)
    kk = [plus(*(scale(a, b) for a, b in zip(r, gg))) for r in rr]
    assert equalspan(localdirs + kk, kernel)
    if expected:
        for name, value in [("complete", complete), ("anchors", anchors), ("generators", generators),
                            ("local_differences", localdirs), ("lifts", lifts)]:
            assert normalize(value) == normalize(expected[name]), name
        for got, want in zip(completion, expected["completion"]):
            assert list(got["coordinates"]) == [int(Fraction(c)) for c in want["coordinates"]]
            assert normalize(got["target"]) == want["target"]
    answer = {"edges": edges, "X": X, "Y": Y, "xe": xe, "ye": ye, "xp": xp,
              "cut": cut, "boundary_order": border, "complete": complete,
              "states": states, "anchors": anchors, "localdirs": localdirs, "Ybasis": Ybasis,
              "A": A, "lifts": lifts, "kernel": kernel, "imagebasis": imagebasis,
              "completion": completion, "residuals": residuals,
              "individual_anchor_changes": anchor_changes,
              "simultaneous_anchor_basis_change": {"relations": rr, "lifts": kk},
              "full": len(full), "survivors": len(survivors), "local_rank": rank(localdirs),
              "kernel_rank": rank(kernel), "image_rank": 9,
              "loss": rank(differences(cycles)) - rank(differences(sorted(survivors)))}
    return answer


def proof_k6(load):
    old = load(BASE + "i176_uniform_five_port_rank/uniform-attempt-02.json")["checks"][0]
    cert = next(c for c in load(BASE + "i176_uniform_five_port_rank/finite-attempt-01.json")["certificates"]
                if c["k"] == 6)
    system = interface(cert["graph"], cert["cut"], sorted(set(v for e in cert["xe"] for v in e)))
    xe, edges = system["xe"], system["edges"]
    X, xp, states = system["X"], system["xp"], system["states"]
    # Expand the actual closed words from U176, not from ancestor Python.
    k, n, j = 6, 5, 3
    T = lambda i: 12 + i
    B = lambda i: 12 + k + i
    p, q = 26, 27
    def t(a, b):
        return [T(i) for i in range(a, b + (1 if b >= a else -1), 1 if b >= a else -1)]
    def b(a, z):
        return [B(i) for i in range(a, z + (1 if z >= a else -1), 1 if z >= a else -1)]
    W = [T(1), B(1), B(2), T(2), T(3), B(3)]
    V = [T(1), T(2), B(2), B(3), T(3)]
    words = {
        "0": [t(1, j) + [p, q] + t(n - 1, n) + b(n, 0)],
        "1a": [[B(0), B(1)] + V + [p, q, T(n - 1), B(n - 1), B(n), T(n)]],
        "1b": [[T(n), T(n - 1), q, p] + t(j, 1) + b(1, n) + [B(0)]],
        "2": [[T(n), T(n - 1), B(n - 1), B(n), B(0), B(1)] + V + [p, q]],
        "3": [[B(0), B(n), T(n), T(n - 1)] + b(n - 1, 1) + t(1, j) + [p, q]],
        "4a": [W + [B(n - 1), B(n), B(0)], [T(n), T(n - 1), q, p]],
        "4b": [t(1, j) + b(j, 0), [T(n), B(n), B(n - 1), T(n - 1), q, p]],
        "5": [W + [B(n - 1), T(n - 1), q, p], [T(n), B(n), B(0)]],
        "6(n-1)": [t(1, j) + [p], [T(n), B(n)] + b(0, n - 1) + [T(n - 1), q]],
        "7Z": [W + [B(n - 1), T(n - 1), T(n), B(n), B(0)], [p, q]],
        "8": [t(1, j) + [p], b(0, n) + [T(n), T(n - 1), q]],
        "9": [[T(n), B(n), B(0)], [p] + t(j, 1) + b(1, n - 1) + [T(n - 1), q]],
        "10a": [[T(n), B(n), B(n - 1), T(n - 1), q], [B(0), B(1)] + V + [p]],
        "10b": [[T(n), T(n - 1), q], [B(0)] + b(n, 1) + t(1, j) + [p]],
    }
    for r in range(1, j):
        words["6r" + str(r)] = [t(1, r) + b(r, 0) + b(n, r + 1) + t(r + 1, j) + [p],
                                [T(n), T(n - 1), q]]
        words["7r" + str(r)] = [t(1, r) + b(r, 0),
                                [p] + t(j, r + 1) + b(r + 1, n) + [T(n), T(n - 1), q]]
    actual = {}
    for w in old["local_witnesses"]:
        name = w["name"]
        key = name
        if name.startswith("6") and name not in words:
            key = "6(n-1)" if name in ("6r4", "64", "6(n-1)") else "6r" + name[-1]
        if name.startswith("7") and name not in words:
            key = "7r" + name[-1]
        val = incidence(xe, words[key])
        assert sorted(v for word in words[key] for v in word) == X
        assert val in states[w["state"]]["X"]
        assert sorted([e for e, z in zip(xe, val) if not z]) == sorted(tuple(e) for e in w["missing"])
        actual[key] = val
    assert len(actual) == 18
    dirs = [minus(actual["6r" + str(r)], actual["6(n-1)"]) for r in (1, 2)]
    dirs += [minus(actual[a], actual[z]) for a, z in (("1a", "1b"), ("4a", "4b"), ("7Z", "7r1"))]
    cols = [xe.index(tuple(e)) for e in old["local_minor_edges"]]
    minor = [[v[i] for i in cols] for v in dirs]
    assert minor == old["local_minor"] and determinant(minor) == -2 and rank(dirs) == 5
    # Proof anchors use specified actual local words and retained actual exterior partners.
    chosen = ["0", "1a", "2", "3", "4a", "5", "6r1", "7Z", "8", "9", "10a"]
    anchors = []
    for i, name in enumerate(chosen):
        c = tuple(old["anchors"][i]["cycle"])
        assert c in states[i]["products"]
        assert tuple(c[edges.index(e)] for e in xe) == actual[name]
        anchors.append(c)
    projection = [edges.index(e) for e in system["ye"]] + [edges.index(e) for e in system["cut"]]
    image = [list(map(Fraction, v)) for v in old["image_directions"]]
    imagecols = old["image_columns"]
    image_minor = [[v[i] for i in imagecols] for v in image]
    assert image_minor == old["image_minor"] and determinant(image_minor) == 1
    # Independently reconstruct their projected actual image vectors using proof anchors.
    proofY = [states[1]["Y"][1], states[4]["Y"][1], states[4]["Y"][2]]
    baseY = [states[1]["Y"][0], states[4]["Y"][0], states[4]["Y"][0]]
    image_new = [list(minus(y, z)) + [0] * 5 for y, z in zip(proofY, baseY)]
    image_new += [[a[j] - anchors[0][j] for j in projection] for a in anchors[1:6] + [anchors[7]]]
    assert image_new == image
    return {"words": words, "local_minor": minor, "local_determinant": -2,
            "image_minor": image_minor, "image_determinant": 1, "anchors": anchors}


def absorption(load, sys, initial):
    data = load(BASE + "i177_adjacent_port_surgery/experiment-attempt-03.json")
    oldedges, newedges = initial["edges"], sys["edges"]
    def transport(v):
        a, b = v[oldedges.index((1, 2))], v[oldedges.index((13, 14))]
        new = {e: v[i] for i, e in enumerate(oldedges) if e in newedges}
        new.update({(1, 28): a, (2, 29): a, (13, 30): b, (14, 31): b,
                    (28, 29): -a, (30, 31): -b, (28, 30): 0, (29, 31): 0})
        result = tuple(new[e] for e in newedges)
        assert all(sum(result[i] for i, e in enumerate(newedges) if v in e) == 0
                   for v in sys["X"] + sys["Y"])
        return result
    assert rank([transport(v) for v in differences(initial["cycles"])]) == 14
    states, xe = sys["states"], sys["xe"]
    def lift(d):
        return tuple(d[xe.index(e)] if e in xe else 0 for e in newedges)
    Xbasis = [lift(minus(states[1]["X"][1], states[1]["X"][0]))] + [
        lift(minus(states[5]["X"][j], states[5]["X"][0])) for j in range(1, 5)]
    actualbasis = Xbasis + sys["Ybasis"] + [sys["A"][i] for i in (1, 2, 3, 4, 5, 7)] + sys["lifts"][:2]
    assert actualbasis == [tuple(map(Fraction, v)) for v in data["actual_ambient_basis"]]
    assert rank(actualbasis) == 16
    representative = initial["survivors"][0]
    olddirs = []
    for item in data["old_defect_absorption"]:
        old = tuple(item["old_direction"])
        assert plus(representative, old) in initial["cycles"]
        got = transport(old)
        assert got == tuple(item["transport"])
        assert got == plus(*(scale(Fraction(c), b) for c, b in zip(item["coefficients"], actualbasis)))
        olddirs.append(old)
    assert rank(initial["L"] + olddirs) == 14 and rank(initial["L"]) == 11
    child = data["child"]
    cb = [tuple(v) for v in child["survivor_basis"]]
    assert all(plus(tuple(child["survivor_anchor"]), v) in set(
        c for s in states for c in s["products"]) for v in cb)
    columns = data["actual_survivor_minor"]["columns"]
    assert determinant([[v[i] for i in columns] for v in cb]) == 2
    rhs = plus(scale(5, Xbasis[0]), *(scale(-1, v) for v in Xbasis[1:]),
               sys["lifts"][0], scale(2, sys["lifts"][1]))
    assert scale(3, sys["lifts"][2]) == scale(3, sys["lifts"][3]) == rhs
    return {"transport_rank": 14, "equations": data["old_defect_absorption"],
            "actual_cycle_determinant": 2, "I177_only_K3_K4_identity": True}


def difference_components(vertices, edges, p, u):
    d = tuple(int(a != b) for a, b in zip(p, u))
    adj = adjacency(vertices, edges, d)
    active = {v: ns for v, ns in adj.items() if ns}
    return [tuple(i for i, e in enumerate(edges) if d[i] and e[0] in comp)
            for comp in components(active)]


def lock(sys, load):
    X, xe, xp = sys["X"], sys["xe"], sys["xp"]
    P = packings(X, xe, xp[:2], [(xp[0], xp[1])])
    S = sys["states"][0]["X"]
    assert len(P) == 5 and len(S) == 1
    s = S[0]
    allmasks, switches, failures, records = 0, 0, 0, []
    for k, p in enumerate(P):
        comps = difference_components(X, xe, p, s)
        masks = []
        for mask in range(1 << len(comps)):
            chosen = set(j for i, comp in enumerate(comps) if mask >> i & 1 for j in comp)
            q = tuple(s[i] if i in chosen else p[i] for i in range(len(xe)))
            v = tuple(p[i] if i in chosen else s[i] for i in range(len(xe)))
            a, b = describe(X, xe, q), describe(X, xe, v)
            good = not a["cycles"] and not b["cycles"]
            assert good == (mask in (0, (1 << len(comps)) - 1))
            if mask.bit_count() == 1:
                switches += 1
                failures += int(not good)
            assert plus(p, s) == plus(q, v)
            masks.append({"mask": mask, "outputs": [a, b], "valid": good})
        allmasks += len(masks)
        # Separate exhaustive difference-EDGE assignments, not component-subset iteration.
        changed = [j for j in range(len(xe)) if p[j] != s[j]]
        admissible = set()
        prescribed = [[sum(vec[j] for j, e in enumerate(xe) if v in e) for v in X]
                      for vec in (p, s)]
        for bits in product((0, 1), repeat=len(changed)):
            q = list(p)
            v = list(s)
            for j, bit in zip(changed, bits):
                q[j], v[j] = bit, 1 - bit
            degrees = [[sum(vec[j] for j, e in enumerate(xe) if z in e) for z in X]
                       for vec in (q, v)]
            if degrees == prescribed or degrees == prescribed[::-1]:
                admissible.add((tuple(q), tuple(v)))
        by_components = set()
        for mask in range(1 << len(comps)):
            chosen = set(j for i, comp in enumerate(comps) if mask >> i & 1 for j in comp)
            by_components.add((tuple(s[j] if j in chosen else p[j] for j in range(len(xe))),
                               tuple(p[j] if j in chosen else s[j] for j in range(len(xe)))))
        assert admissible == by_components
        records.append({"P_index": k, "p": describe(X, xe, p), "components":
                        [[xe[j] for j in comp] for comp in comps], "masks": masks,
                        "independent_edge_assignments": len(admissible)})
    assert (allmasks, switches, failures) == (18, 9, 8)
    parent = load(BASE + "i179-parent-helper.json")
    w = parent["witness"]
    assert incidence(xe, w["p"]) == P[0] and incidence(xe, w["s"]) == s
    return {"P": P, "state0": s, "records": records, "masks": allmasks,
            "single_switches": switches, "isolated_cycle_failures": failures}


def parent_helper(sys, locked, load):
    xe, X, states, P = sys["xe"], sys["X"], sys["states"], locked["P"]
    original = load(BASE + "i179-parent-helper.json")
    solutions = []
    for j, q in enumerate(P[1:], 1):
        changed = tuple(i for i in range(len(xe)) if P[0][i] != q[i])
        for i, state in enumerate(states):
            for a, u in enumerate(state["X"]):
                for b, v in enumerate(state["X"]):
                    if plus(P[0], u) != plus(q, v):
                        continue
                    comps = difference_components(X, xe, P[0], u)
                    iscycle = changed in comps and all(
                        sum(z in xe[t] for t in changed) in (0, 2) for z in X)
                    solutions.append({"P_index": j, "state": i, "u_index": a, "up_index": b,
                                      "changed_edges": [xe[t] for t in changed],
                                      "single_alternating_cycle": iscycle})
    assert normalize(solutions) == original["solutions"]
    assert len(solutions) == 12 and sum(s["single_alternating_cycle"] for s in solutions) == 3
    for key, typ in (("p", 0), ("pp", 0), ("u", 5), ("up", 5), ("s", -1)):
        vec = incidence(xe, original["witness"][key])
        info = describe(X, xe, vec)
        assert not info["cycles"]
        assert vec in (P if typ == 0 else states[0 if typ == -1 else typ]["X"])
    return {"solutions": solutions, "witness": original["witness"],
            "already_parent_work": True}


def mandatory(load):
    expected = load(BASE + "i179_path_recombination/mandatory-attempt-09.json")
    result, order = {}, []
    graphs = load(BASE + "i166_affine_span_braces/bracegen-graphs.json")["bfs"]
    graphs = {v["history"]: v for v in graphs.values()}
    steps = load(BASE + "i167_exchange_step_braces/diagnostic-attempt-01.json")["expansions"]
    result["controls"] = []
    for idx, wanted in zip(ORDER, expected["controls"]):
        item = steps[idx]
        graph = graphs[item["parent_history"]]
        ans, _ = control(graph, terminal_order(graph, item["step"]), wanted)
        result["controls"].append(dict(ans, index=idx))
        order.append(idx)
    data = load(BASE + "i172_prescribed_square_switch/mandatory-attempt-01.json")["C171"]
    ans, calc = control(data["graph"], terminal_order(data["graph"], data["row"]["step"]),
                        expected["C171"])
    vertices, edges = calc["vertices"], calc["edges"]
    w = tuple(map(Fraction, data["w"]))
    C0 = tuple(data["C0"])
    F, T = tuple(data["F"]), tuple(data["T"])
    assert F != T
    assert sum(a * b for a, b in zip(w, minus(F, C0))) == Fraction(1, 14)
    assert sum(a * b for a, b in zip(w, minus(T, C0))) == Fraction(-1, 2)
    assert all(sum(a * b for a, b in zip(w, d)) == 0 for d in calc["L"] + calc["V"])
    assert len(components(adjacency(vertices, edges, F))) == len(components(adjacency(vertices, edges, T))) == 2
    assert all(sum(z[i] for i, e in enumerate(edges) if v in e) == 2 for z in (F, T) for v in vertices)
    uvxy = terminal_order(data["graph"], data["row"]["step"])
    u, v, x, y = uvxy
    square = {edge(u, v), edge(v, y), edge(y, x), edge(x, u)}
    pre = tuple(1 - a if e in square else a for e, a in zip(edges, F))
    assert pre in calc["families"]["N00"]
    brace = load(BASE + "i171_square_switch_weight/brace-certificate-attempt-01.json")
    ans["matching_extensions"] = matching_check(vertices, edges, brace["extensions"])
    ans["switch"] = {"F_weight": "1/14", "T_weight": "-1/2", "precycle": pre, "square": sorted(square)}
    result["C171"] = ans
    order.append("C171")
    octs = load(BASE + "i172_prescribed_square_switch/cut-octagons-attempt-01.json")["records"]
    result["G6_G10"] = []
    for j, item in enumerate([octs[1], octs[3]]):
        ans, calc = control(item["graph"], terminal_order(item["graph"], item["row"]["step"]),
                            expected["G6_G10"][j], item)
        matchings = degree_vectors(calc["vertices"], calc["edges"], {v: 1 for v in calc["vertices"]})
        uncovered = next((a, b) for a, b in combinations(range(len(calc["edges"])), 2)
                         if not set(calc["edges"][a]) & set(calc["edges"][b])
                         and not any(m[a] and m[b] for m in matchings))
        ans["nonbrace_pair"] = [calc["edges"][t] for t in uncovered]
        ans["perfect_matchings_exhausted"] = len(matchings)
        result["G6_G10"].append(ans)
    order.append("G6/G10")
    data = load(BASE + "i175_affected_prism_exterior/experiment-attempt-01.json")["first_children"][0]
    result["first_P8"], _ = control(data["graph"], data["uvxy"], expected["first_P8"], data,
                                    data["brace"]["extensions"])
    order.append("first_P8")
    result["I176_k6"] = proof_k6(load)
    order.append("I176_k6")
    old = load(BASE + "i177_adjacent_port_surgery/experiment-attempt-03.json")
    data = old["child"]
    result["I177"], _ = control(data["graph"], data["uvxy"], expected["I177"], data,
                               data["brace"]["extensions"])
    result["I177_initial"], initial = control(old["initial"]["graph"], old["initial"]["uvxy"],
                                              expected["I177_initial"], old["initial"])
    system = interface(data["graph"], old["fiveport"]["cut"], old["fiveport"]["X"], expected["I178"])
    result["I177_absorption"] = absorption(load, system, initial)
    order.append("I177_child_absorption")
    result["I178"] = system
    order.append("I178_relations_completion")
    result["I179_lock"] = lock(system, load)
    order.append("I179_lock")
    result["parent_helper"] = parent_helper(system, result["I179_lock"], load)
    order.append("parent_helper")
    result["order"] = order
    result["status"] = "PASS"
    return normalize(result)


def calibration(load):
    old = load(BASE + "i177_adjacent_port_surgery/experiment-attempt-03.json")
    sys = interface(old["child"]["graph"], old["fiveport"]["cut"], old["fiveport"]["X"])
    X, xe, xp, states = sys["X"], sys["xe"], sys["xp"], sys["states"]
    P = packings(X, xe, xp[:2], [(xp[0], xp[1])])
    witnesses, rejected, edges = [], [], set()
    for a, p in enumerate(P):
        for i, state in enumerate(states):
            for b, u in enumerate(state["X"]):
                comps = difference_components(X, xe, p, u)
                for comp in comps:
                    if not all(sum(v in xe[j] for j in comp) in (0, 2) for v in X):
                        continue
                    assert all(sum((p[j] - u[j]) for j in comp if v in xe[j]) == 0 for v in X)
                    q = tuple(u[j] if j in comp else p[j] for j in range(len(xe)))
                    v = tuple(p[j] if j in comp else u[j] for j in range(len(xe)))
                    qinfo, vinfo = describe(X, xe, q), describe(X, xe, v)
                    assert plus(p, u) == plus(q, v)
                    valid = q in P and v in state["X"]
                    info = {"p_index": a, "state": i, "u_index": b,
                            "cycle_edges": [xe[j] for j in comp],
                            "q": qinfo, "v": vinfo, "valid": valid}
                    if valid:
                        c, d = P.index(q), state["X"].index(v)
                        assert c != a
                        assert qinfo["pairing"] == [(xp[0], xp[1])]
                        assert not qinfo["cycles"] and not vinfo["cycles"]
                        assert noncrossing(TYPES[i][1])
                        edges.add(edge(a, c))
                        info.update(q_index=c, v_index=d, p=describe(X, xe, p), u=describe(X, xe, u))
                        witnesses.append(info)
                    else:
                        rejected.append(info)
    # Independently exhaust every exact four-packing identity, then test the whole-component criterion.
    alternative = set()
    for a, c in combinations(range(len(P)), 2):
        p, q = P[a], P[c]
        changed = {j for j in range(len(xe)) if p[j] != q[j]}
        for i, state in enumerate(states):
            for b, u in enumerate(state["X"]):
                for d, v in enumerate(state["X"]):
                    if plus(p, u) != plus(q, v):
                        continue
                    adj = adjacency(X, [xe[j] for j in sorted(changed)])
                    active = {z: ns for z, ns in adj.items() if ns}
                    if not active or any(len(ns) != 2 for ns in active.values()) or len(components(active)) != 1:
                        continue
                    # No extra difference edge may attach: required by "one WHOLE component".
                    if any(p[j] != u[j] and j not in changed and (xe[j][0] in active or xe[j][1] in active)
                           for j in range(len(xe))):
                        continue
                    alternative.add((a, c, i, b, d))
    canonical = {(w["p_index"], w["q_index"], w["state"], w["u_index"], w["v_index"])
                 for w in witnesses if w["p_index"] < w["q_index"]}
    assert canonical == alternative
    adj = adjacency(list(range(len(P))), sorted(edges))
    comps = components(adj)
    WX = [tuple(v[sys["edges"].index(e)] for e in xe) for v in sys["localdirs"]]
    weak = rank(WX + differences(P)) == rank(WX)
    hamming = [[sum(x != y for x, y in zip(p, q)) for q in P] for p in P]
    parent_locked = []
    for i in (5, 6, 9):
        for j in (2, 3, 4):
            assert plus(P[0], states[i]["X"][j]) == plus(P[j], states[i]["X"][0])
            assert not any(w["p_index"] == 0 and w["state"] == i and w["u_index"] == j
                           for w in witnesses)
            parent_locked.append({"state": i, "P_index": j, "u_index": j,
                                  "v_index": 0, "no_legal_first_same_pair_cycle_move": True})
    # Provide actual chain certificates without interpreting rank as connectivity.
    chains = []
    for a in range(len(P)):
        parents = {a: None}
        queue = [a]
        for b in queue:
            for c in adj[b]:
                if c not in parents:
                    parents[c] = b
                    queue.append(c)
        chains.append({"root": a, "parents": {str(k): v for k, v in parents.items()}})
    return normalize({"status": "PASS", "new_graphs": 0, "scope": "Complete retained I177 helper graph only",
                      "P": [{"vector": p, "paths": describe(X, xe, p)["paths"]} for p in P],
                      "edges": sorted(edges), "components": comps, "connected": len(comps) == 1,
                      "witnesses": witnesses, "rejected_cycle_moves": rejected,
                      "independent_identity_enumeration": sorted(alternative), "chains": chains,
                      "WX_rank": rank(WX), "P_difference_rank": rank(differences(P)),
                      "hamming_distance": hamming,
                      "nine_parent_identities_fixed_pair_lock": parent_locked,
                      "weaker_containment": weak, "H180_universal_verdict": "UNRESOLVED"})
