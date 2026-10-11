"""Bounded retained controls, reconstructed from prose and frozen JSON.

Loads exact.py, geometry.py and indexed.py in the same namespace.
No pre-I183 implementation is compiled, executed or copied.
"""
REF = "frontier/experiments/i182_controlled_extension/mandatory-attempt-05.json"
P171 = "frontier/experiments/i171_square_switch_weight/"
P175 = "frontier/experiments/i175_affected_prism_exterior/"
P176 = "frontier/experiments/i176_uniform_five_port_rank/"
P177 = "frontier/experiments/i177_adjacent_port_surgery/"


def from_graph(graph, name, labels=None, step=None):
    if labels is None:
        f, i, j = step
        face = graph["faces"][f]
        labels = [face[i], face[(i+1) % len(face)],
                  face[(j+1) % len(face)], face[j]]
    return {"parent_edges": graph["edges"], "faces": graph["faces"],
            "index": name, "labels": labels}


def dot(a, b):
    return sum(Fraction(x)*Fraction(y) for x, y in zip(a, b))


def bits_for(edges, chosen):
    chosen = {tuple(e) for e in chosen}
    assert chosen <= set(edges)
    return tuple(int(e in chosen) for e in edges)


def calibration(read_json):
    reference = read_json(REF)
    witness = read_json(P171+"weight-obstruction-attempt-01.json")[
        "witnesses"]["two_component_forbidden_weight"]
    raw = from_graph(witness["graph"], "C171", step=witness["step"])
    out = control(raw, reference["C171"])
    edges = [tuple(e) for e in raw["parent_edges"]]
    vertices = sorted({v for e in edges for v in e})
    cert = read_json(P171+"brace-certificate-attempt-01.json")
    assert cert["graph"]["edges"] == raw["parent_edges"]
    count = check_extensions(edges, cert["extensions"])
    assert count == 1032
    c0 = tuple(witness["C0"])
    n = tuple(witness["N"])
    t = bits_for(edges, witness["factor_edges"])
    assert c0 in out["cycles"] and n in out["families"]["N00"]
    u, v, x, y = raw["labels"]
    s = tuple(int(e in (edge(u, v), edge(x, y))) -
              int(e in (edge(u, x), edge(v, y))) for e in edges)
    f = plus(n, s)
    for z in (f, t):
        assert set(z) <= {0, 1}
        sig = signature(vertices, [e for e, b in zip(edges, z) if b])
        assert len(sig["cycles"]) == 2 and not sig["paths"] and not sig["singletons"]
    w = list(map(Fraction, witness["w"]))
    assert dot(w, minus(n, c0)) == 1
    assert dot(w, minus(f, c0)) == Fraction(1, 14)
    assert dot(w, minus(t, c0)) == Fraction(-1, 2) and f != t
    fs = out["families"]
    survivors = sorted(fs["N10"]+fs["N01"]+fs["N11"])
    assert all(dot(w, z) == 0 for z in
               differences(survivors)+differences(fs["N00"]))
    out.update({"extensions": count, "F_weight": "1/14", "T_weight": "-1/2"})
    records = read_json(
        "frontier/experiments/i172_prescribed_square_switch/"
        "residual-certificates-attempt-01.json")["records"]
    nonbraces = []
    for k, expected in zip((6, 10), reference["G6_G10"]):
        row = next(z for z in records if z["L"] == k)
        raw = from_graph(row["graph"], "G"+str(k), step=row["row"]["step"])
        result = control(raw, expected)
        ee = [tuple(e) for e in raw["parent_edges"]]
        vv = sorted({v for e in ee for v in e})
        matchings = factors(vv, ee, {v: 1 for v in vv})
        assert isinstance(expected["perfect_matchings"], int)
        assert len(matchings) == expected["perfect_matchings"]
        pair = [ee.index(tuple(e)) for e in expected["nonbrace_pair"]]
        assert set(ee[pair[0]]).isdisjoint(ee[pair[1]])
        assert all(not (m[pair[0]] and m[pair[1]]) for m in matchings)
        assert result["values"]["ell"] == k-3
        result.update({"perfect_matchings": len(matchings),
                       "nonbrace_pair": expected["nonbrace_pair"]})
        nonbraces.append(result)
    first = read_json(P175+"experiment-attempt-01.json")["first_children"][0]
    raw = from_graph(first["graph"], "first_P8", first["uvxy"])
    p8 = control(raw, reference["first_P8"])
    p8["extensions"] = check_extensions(
        [tuple(e) for e in raw["parent_edges"]], first["brace"]["extensions"])
    assert p8["extensions"] == 900
    return {"status": "PASS", "order": ["C171", "G6/G10", "first_P8"],
            "C171": out, "G6_G10": nonbraces, "first_P8": p8}


def uniform6(read_json):
    ref = read_json(REF)["I176_k6"]
    data = read_json(P176+"uniform-attempt-02.json")
    check = next(x for x in data["checks"] if x["k"] == 6)
    T = lambda i: 12+i
    B = lambda i: 18+i
    p, q, s, t = 26, 27, 24, 25
    xe = sorted([edge(T(i), B(i)) for i in range(1, 6)] +
                [edge(T(i), T(i+1)) for i in (1, 2, 4)] +
                [edge(B(i), B((i+1) % 6)) for i in range(6)] +
                [edge(T(3), p), edge(p, q), edge(q, T(4))])
    ye = [tuple(e) for e in data["fixed_exterior"]]
    # The retained fixed exterior uses the base k=6 labels 24,25.
    cut = [edge(1, T(1)), edge(5, T(5)), edge(6, B(0)),
           edge(s, p), edge(t, q)]
    edges = sorted(xe+ye+cut)
    vertices = sorted({v for e in edges for v in e})
    X = sorted({v for e in xe for v in e})
    assert len(edges) == 39 and len(vertices) == 26 and len(X) == 13
    local = {}
    for item in check["local_witnesses"]:
        words = item["path_words"]
        assert sorted(v for word in words for v in word) == X
        chosen = [edge(a, b) for word in words for a, b in zip(word, word[1:])]
        bits = bits_for(xe, chosen)
        assert [list(e) for e, b in zip(xe, bits) if not b] == item["missing"]
        name = "6(n-1)" if item["name"] == "6r4" else item["name"]
        assert words == ref["words"][name]
        local[name] = bits
        st = check["states"][item["state"]]
        assert list(bits) in st["X"]
        y = st["Y"][item["exterior_partner_index"]]
        selected = [e for e, b in zip(xe, bits) if b] + [
            e for e, b in zip(ye, y) if b] + [cut[j] for j in st["J"]]
        sig = signature(vertices, selected)
        assert len(sig["cycles"]) == 1 and not sig["paths"] and not sig["singletons"]
        assert 2 in st["J"] or edge(1, 7) in selected
    directions = [minus(local["6r"+str(i)], local["6(n-1)"]) for i in (1, 2)]
    directions += [minus(local[a], local[b]) for a, b in
                   (("1a", "1b"), ("4a", "4b"), ("7Z", "7r1"))]
    cols = [xe.index(tuple(e)) for e in check["local_minor_edges"]]
    minor = [[z[j] for j in cols] for z in directions]
    assert minor == check["local_minor"] == ref["local_minor"]
    assert determinant(minor) == -2
    anchors = []
    for item in check["anchors"]:
        i = item["state"]
        name = item["local_template"]
        name = "6(n-1)" if name == "6r4" else name
        z = bits_for(edges, [e for e, b in zip(xe, local[name]) if b] +
                     [e for e, b in zip(ye, item["Y"]) if b] +
                     [cut[j] for j in check["states"][i]["J"]])
        assert list(z) == item["cycle"] == ref["anchors"][i]
        anchors.append(z)
    image = []
    for state, which in ((1, 1), (4, 1), (4, 2)):
        ys = check["states"][state]["Y"]
        delta = minus(ys[which], ys[0])
        image.append(tuple(delta[ye.index(e)] if e in ye else 0 for e in edges))
    image += [minus(anchors[i], anchors[0]) for i in (1, 2, 3, 4, 5, 7)]
    cols = [edges.index(ye[j]) for j in check["image_columns"]]
    im = [[z[j] for j in cols] for z in image]
    assert im == ref["image_minor"]
    assert [[Fraction(x) for x in row] for row in check["image_minor"]] == im
    assert determinant(im) == 1
    return {"status": "PASS", "k": 6, "words": len(local),
            "anchors": anchors, "local_minor": minor, "image_minor": im,
            "determinants": [-2, 1]}
