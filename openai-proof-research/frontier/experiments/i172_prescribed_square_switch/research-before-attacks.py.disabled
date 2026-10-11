"""Diagnostics; toolkit symbols and authenticated load() supplied by runner."""
MANDATORY = [0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539, 431]
I171 = "frontier/experiments/i171_square_switch_weight/"
GRAPHS = "frontier/experiments/i166_affine_span_braces/bracegen-graphs.json"
I167 = "frontier/experiments/i167_exchange_step_braces/diagnostic-attempt-01.json"


def compare(row, expected):
    for k in ("n", "step", "counts", "dg", "rankL", "rankU", "rankUV",
              "ell", "t", "eta", "arcs", "face_length", "delta_V", "delta_R",
              "epsilon", "classes", "alpha", "weight"):
        if k in expected:
            assert row[k] == expected[k], (k, row.get("step"), row.get(k), expected[k])


def mandatory():
    original = load(I167)["expansions"]
    records = list(load(GRAPHS)["bfs"].values())
    by_history = {r["history"]: r for r in records}
    graphs = {}
    expected = load(I171+"mandatory-attempt-01.json")["first"]
    results = []
    for idx, old in zip(MANDATORY, expected):
        exp = original[idx]
        h = exp["parent_history"]
        if h not in graphs:
            graphs[h] = Graph(by_history[h])
            graphs[h].validate()
        row = analyze(graphs[h], exp["step"])
        compare(row, old)
        results.append(dict(index=idx, row=row))
    witness = load(I171+"weight-obstruction-attempt-01.json")["witnesses"]["two_component_forbidden_weight"]
    g = Graph(witness["graph"])
    g.validate()
    row, detail = analyze(g, witness["step"], True)
    compare(row, witness["row"])
    C0, N = tuple(witness["C0"]), tuple(witness["N"])
    w = tuple(map(Q, witness["w"]))
    assert C0 in g.cycles() and N in detail["families"]["N00"]
    assert all(dot(w, z) == 0 for z in detail["L"]+detail["V"])
    assert dot(w, sub(N, C0)) == 1
    T = g.vector(witness["factor_edges"])
    u, v, x, y = g.families(witness["step"])[1]
    s = sub(add(g.unit(u, v), g.unit(x, y)), add(g.unit(u, x), g.unit(v, y)))
    F = add(N, s)
    assert T in g.factors and F in g.factors and F != T
    assert len(g.components(T)) == len(g.components(F)) == 2
    assert dot(w, sub(T, C0)) == Q(-1, 2)
    assert dot(w, sub(F, C0)) == Q(1, 14)
    matchings = g.matchings()
    extensions = []
    for i, e in enumerate(g.edges):
        for j in range(i+1, g.m):
            if set(e).isdisjoint(g.edges[j]):
                M = next(M for M in matchings if M[i] and M[j])
                extensions.append(dict(pair=[i, j], matching=list(M)))
    assert (len(g.cycles()), len(matchings), len(extensions)) == (110, 1007, 1032)
    guide = load(I171+"guide-attempt-01.json")
    z = Graph(guide["graph"])
    z.validate()
    guide_row, gd = analyze(z, guide["row"]["step"], True)
    compare(guide_row, guide["row"])
    sep = guide["bridge_separator"]
    assert all(dot(sep["w"], a) == 0 for a in gd["L"]+gd["U"])
    assert dot(sep["w"], sep["b"]) == dot(sep["w"], gd["b"]) == 10
    # Compare the retained orientation, not the opposite fresh sorting.
    old_cycles = [z.vector(o["cycle"]) for o in guide["old_cycles"]]
    assert set(old_cycles) == set(gd["families"]["N00"])
    old_direction = sub(old_cycles[1], old_cycles[0])
    assert dot(sep["w"], old_direction) == 8
    assert rank(gd["L0"]+gd["U"]) == rank(gd["L0"]) == 8
    assert all(a["good_count"] == 0 for a in guide_row["classes"].values())
    # Retained and fresh bridges have identical class modulo L+U.
    assert rank(gd["L"]+gd["U"]+[sub(sep["b"], gd["b"])]) == rank(gd["L"]+gd["U"])
    return dict(order=MANDATORY, census=results,
                C171=dict(row=row, graph=witness["graph"], cycles=g.cycles(),
                          matchings=matchings, extensions=extensions, w=list(map(str, w)),
                          C0=C0, N=N, F=F, T=T, F_weight="1/14", T_weight="-1/2",
                          F_components=g.components(F), T_components=g.components(T)),
                index431=dict(row=guide_row, graph=guide["graph"], cycles=z.cycles(),
                              families=gd["families"], toggles=gd["toggles"],
                              separator=sep, old_direction=old_direction,
                              bridge_pairing=10, old_pairing=8))


def populations():
    # Mandatory diagnostics always precede even this audit, not just research.
    first = mandatory()
    records = load(GRAPHS)
    bfs = list(records["bfs"].values())
    walks = [g for g in records["walks"].values() if g["n"] <= 32]
    cache = {}

    def graph(record):
        key = tuple(map(tuple, record["edges"]))
        if key not in cache:
            g = Graph(record)
            g.validate()
            cache[key] = g
        return cache[key]

    old_square = load(I171+"weights-attempt-01.json")
    square_rows, square_records = [], [g for g in walks if g["n"] == 32]
    weight_histograms = []
    for record in square_records:
        g = graph(record)
        for step in steps(record, 4):
            row, detail = analyze(g, step, True)
            expected = old_square["rows"][len(square_rows)]
            assert record["history"] == expected["history"]
            compare(row, expected)
            if row["alpha"] is not None:
                cert = expected["weight_certificate"]
                w = tuple(map(Q, cert["w"]))
                assert all(not dot(w, z) for z in detail["L"]+detail["V"])
                assert dot(w, sub(detail["families"]["N00"][0], detail["C0"])) == 1
                histogram = dict(sorted(Counter(str(dot(w, sub(T, detail["C0"])))
                                                for T in g.factors).items()))
                assert histogram == cert["twofactor_weight_histogram"]
                weight_histograms.append(histogram)
            square_rows.append(dict(history=record["history"], **row))
    assert len(square_records) == 38 and len(square_rows) == 806
    assert Counter(r["alpha"] for r in square_rows) == {None: 342, "-13/14": 464}
    oct_old = load(I171+"octagons-attempt-01.json")
    oct_rows = []
    for parent_index, record in enumerate(bfs+walks):
        g = graph(record)
        for step in steps(record, minimal=True):
            row = analyze(g, step)
            expected = oct_old["rows"][len(oct_rows)]
            assert expected["parent_record"] == parent_index
            compare(row, expected)
            oct_rows.append(dict(parent_record=parent_index, **row))
    assert len(oct_rows) == 624
    root = load(I171+"guide-attempt-01.json")["graph"]
    face = root["faces"][0]
    protected = {edge(a, b) for a, b in zip(face, face[1:]+face[:1])}
    levels = [[root]]
    seen = {tuple(map(tuple, root["edges"]))}
    generated = []
    for depth in (1, 2, 3):
        children = []
        parents = levels[-1] if depth == 1 else levels[-1][:6]
        for parent in parents:
            choices = []
            for step in steps(parent, 4):
                f = parent["faces"][step[0]]
                deleted = {edge(f[k], f[(k+1) % len(f)]) for k in step[1:]}
                if not deleted & protected:
                    choices.append(step)
            if depth == 3:
                choices = choices[:4]
            for step in choices:
                child = expand(parent, step, "I171")
                key = tuple(map(tuple, child["edges"]))
                if key in seen:
                    continue
                seen.add(key)
                children.append(child)
                generated.append((depth, child))
        levels.append(children)
    assert list(map(len, levels)) == [1, 8, 64, 24]
    targeted_old = load(I171+"targeted-attempt-01.json")["records"]
    target_rows = []
    for (depth, record), retained in zip(generated, targeted_old):
        assert record["edges"] == [tuple(e) for e in retained["graph"]["edges"]]
        assert record["faces"] == retained["graph"]["faces"]
        g = graph(record)
        fi = next(i for i, f in enumerate(record["faces"]) if f == face)
        row = analyze(g, (fi, 0, 4))
        compare(row, retained["row"])
        target_rows.append(dict(depth=depth, graph=record, row=row))
    assert len(generated) == len(targeted_old) == len(target_rows) == 96

    def histogram(rows, keys):
        return dict(sorted(Counter(str(tuple(r[k] for k in keys)) for r in rows).items()))

    oct_hist = histogram(oct_rows, ("ell", "t", "eta"))
    oct_deficit = histogram(oct_rows, ("delta_V", "delta_R", "epsilon"))
    target_hist = histogram([r["row"] for r in target_rows], ("ell", "t", "eta"))
    target_deficit = histogram([r["row"] for r in target_rows], ("delta_V", "delta_R", "epsilon"))
    assert oct_hist == oct_old["histogram"] and oct_deficit == oct_old["deficit_histogram"]
    target_payload = load(I171+"targeted-attempt-01.json")
    assert target_hist == target_payload["histogram"] and target_deficit == target_payload["deficit_histogram"]
    return dict(mandatory_passed=True, square_rows=square_rows,
                square_histogram=histogram(square_rows, ("ell", "t", "eta")),
                equality_count=464, square_weight_histograms=weight_histograms,
                octagon_rows=oct_rows, octagon_histogram=oct_hist,
                octagon_deficit_histogram=oct_deficit, targeted=target_rows,
                targeted_histogram=target_hist, targeted_deficit_histogram=target_deficit,
                generation_levels=list(map(len, levels)),
                independently_enumerated_graphs=[dict(graph=g.record, cycles=g.cycles())
                                                  for g in cache.values()])
