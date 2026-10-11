# Adapted from authenticated same-I183 resumed/indexed.py; finalization scope.
"""Fresh first twelve controls. Loaded with the owned exact.py namespace."""
import json

ORDER = [0, 520, 522, 524, 527, 528, 530, 533, 534, 536, 539, 431]
ALL_STAGES = ORDER + [
    "C171", "G6/G10", "first_P8", "I176_k6", "I177_child_absorption",
    "I178_relations_completion", "I179_lock", "parent_helper",
    "I180_helpergraph", "I181_patch_reattachment", "I182_reduction_finite"]


def normalize(value):
    return json.loads(json.dumps(value))


def control(raw, expected):
    edges = [tuple(e) for e in raw["parent_edges"]]
    assert edges == sorted(set(edges))
    vertices = sorted({v for e in edges for v in e})
    geometry_check = embedding(edges, raw["faces"])
    geometry = facial_arcs(edges, raw["faces"], raw["labels"])
    u, v, x, y = raw["labels"][:4]
    deleted = (edge(u, v), edge(x, y))
    e, f = [edges.index(z) for z in deleted]
    ke = [z for z in edges if z not in deleted]
    pos = [edges.index(z) for z in ke]

    def embed(bits):
        out = [0] * len(edges)
        for j, bit in zip(pos, bits):
            out[j] = bit
        return tuple(out)

    cs = family(vertices, edges)
    fs = {name: [] for name in ("N00", "N10", "N01", "N11")}
    for c in cs:
        fs["N" + str(c[e]) + str(c[f])].append(c)
    for name, ends, pairing in (
            ("Pux", (u, x), [edge(u, x)]),
            ("Pvy", (v, y), [edge(v, y)]),
            ("D11", (u, v, x, y), [edge(u, v), edge(x, y)])):
        fs[name] = [embed(z) for z in family(vertices, ke, ends, pairing)]
    assert normalize(cs) == expected["cycles"]
    assert normalize(fs) == expected["families"]
    survivors = sorted(fs["N10"] + fs["N01"] + fs["N11"])
    l = differences(survivors)
    l0 = sum((differences(fs[n]) for n in ("N10", "N01", "N11")), [])
    vs = differences(fs["N00"])
    us = sum((differences(fs[n]) for n in ("Pux", "Pvy", "D11")), [])
    c0 = survivors[0]
    a, b0, c0three = (fs[n][0] for n in ("N10", "N01", "N11"))
    n0, p, q, d = (fs[n][0] for n in ("N00", "Pux", "Pvy", "D11"))
    two = tuple(2 if j in (e, f) else 0 for j in range(len(edges)))
    bridge = minus(plus(p, q, d, two), times(3, c0))
    beta = minus(plus(p, q, d, two), plus(a, b0, c0three))
    c = plus(n0, times(-1, a), times(-1, b0), c0three)
    assert list(bridge) == expected["b"]
    assert list(beta) == expected["beta"]
    assert list(c) == expected["c"]
    for z in (bridge, beta, c):
        assert all(sum(z[j] for j, en in enumerate(edges) if w in en) == 0
                   for w in vertices)
    assert rank(l + [minus(bridge, beta)]) == rank(l)
    assert rank([(z[e], z[f]) for z in l]) == 2
    assert rank(l) == rank(l0) + 2
    vg, residual_space = [], []
    residuals = {}
    for name in ("Pux", "Pvy", "D11"):
        arc = geometry["vectors"][name]
        assert list(arc) == expected["residuals"][name]["q"]
        assert arc[e] == arc[f] == 0
        degrees = {w: sum(arc[j] for j, en in enumerate(edges) if w in en)
                   for w in vertices}
        wanted_ends = {"Pux": (u, x), "Pvy": (v, y),
                       "D11": (u, v, x, y)}[name]
        assert degrees == {w: int(w in wanted_ends) for w in vertices}
        good = [z for z in fs["N00"] if minus(z, arc) in fs[name]]
        anchor = minus(good[0], arc) if good else fs[name][0]
        residual = [z for z in fs[name] if plus(z, arc) not in good]
        rdirs = [minus(z, anchor) for z in residual]
        payload = {"q": arc, "good": good, "anchor": anchor,
                   "residual": residual, "residual_directions": rdirs}
        assert normalize(payload) == expected["residuals"][name]
        translated = [minus(z, arc) for z in good]
        assert rank(differences(translated) + rdirs) == rank(differences(fs[name]))
        assert rank(differences(fs[name]) + differences(translated) + rdirs) == \
            rank(differences(fs[name]))
        vg += differences(good)
        residual_space += rdirs
        residuals[name] = len(residual)
    assert rank(us + vg + residual_space) == rank(us) == rank(vg + residual_space)
    assert rank(vs + vg) == rank(vs)
    r_l, r_u, r_lu, r_lv = rank(l), rank(us), rank(l + us), rank(l0 + vs)
    dg = rank(differences(cs))
    ell, t = dg - r_l, r_lu - r_l
    dv = r_lv - rank(l0 + vg)
    dr = rank(l0 + vg + residual_space) - rank(l0 + vg)
    epsilon = rank(l0 + vs + [c]) - r_lv
    eta = rank(l + us + [bridge]) - r_lu
    assert dg == 2 + rank(l0 + vs + [c])
    assert r_lu == 2 + rank(l0 + us)
    assert eta == rank(l0 + us + [beta]) - rank(l0 + us)
    assert ell - t == dv + epsilon - dr
    result = {"dg": dg, "rankL": r_l, "rankL0": rank(l0), "rankU": r_u,
              "rankUV": rank(us + vs), "ell": ell, "t": t, "eta": eta,
              "delta_V": dv, "delta_R": dr, "epsilon": epsilon,
              "counts": {k: len(vv) for k, vv in fs.items()}}
    for key, value in result.items():
        assert value == expected["row"][key], (raw["index"], key, value)
    if raw["index"] == 431:
        assert rank(us + vs) > rank(us)
        assert rank(l + us + vs) > rank(l + us)
        assert all(not expected["residuals"][name]["good"]
                   for name in ("Pux", "Pvy", "D11"))
    return {"index": raw["index"], "values": result, "residual_counts": residuals,
            "b": bridge, "beta": beta, "c": c,
            "arc_geometry": geometry, "embedding": geometry_check,
            "cycles": cs, "families": fs,
            "status": "PASS"}


def indexed(read_json):
    old = read_json("frontier/experiments/i169_bridge_independence/audit-attempt-02.json")
    reference = read_json("frontier/experiments/i182_controlled_extension/mandatory-attempt-05.json")
    selected = {r["index"]: r for r in old["rows"] if r["index"] in ORDER}
    assert set(selected) == set(ORDER)
    out = []
    for index, expected in zip(ORDER, reference["controls"]):
        selected[index]["faces"] = graph_by_edges(
            read_json, selected[index]["parent_edges"])["faces"]
        out.append(control(selected[index], expected))
    return {"status": "PASS_PREFIX_ONLY", "order": ORDER, "controls": out,
            "remaining_stages": ALL_STAGES[len(ORDER):],
            "limitation": "This is not the complete 23-stage mandatory replay."}
