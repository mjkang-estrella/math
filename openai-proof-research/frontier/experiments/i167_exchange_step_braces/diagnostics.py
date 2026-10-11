"""Read-only independent audit and targeted exchange diagnostics."""
import ast
import hashlib
import itertools
import json
from pathlib import Path
import runpy

HERE = Path(__file__).resolve().parent
ROOT = HERE.parents[2]
OLD = ROOT / "frontier/experiments/i166_affine_span_braces"
K = runpy.run_path(str(HERE / "kernel.py"))
globals().update({name: obj for name, obj in K.items() if not name.startswith("_")})


def load(name):
    return json.loads((OLD / name).read_text())


def switch_rank(es, hs):
    rows = []
    pairs = 0
    for a, b in itertools.combinations(hs, 2):
        if connected(selected(es, a ^ b)):
            pairs += 1
            rows.append([((b >> i) & 1)-((a >> i) & 1) for i in range(len(es))])
    return rank(rows), pairs


def diagnose(faces, dual=True):
    n = certify(faces)
    es = edges(faces)
    hs = cycles(es)
    if dual:
        assert hs == cycles_dfs(es)
    d = dimension(es, hs)
    return {"n": n, "h": len(hs), "d": d, "brace": brace(es)}


def cube_anchor():
    fs = [[0, 1, 3, 2], [4, 6, 7, 5], [0, 4, 5, 1],
          [2, 3, 7, 6], [0, 2, 6, 4], [1, 5, 7, 3]]
    assert diagnose(fs) == {"n": 8, "h": 6, "d": 5, "brace": True}
    assert rank([[2, 4], [3, 6]]) == 1
    assert rank([[1, 1, 0], [1, 0, 1], [0, 1, 1]]) == 3
    assert rank([[1, 1, 0], [1, 0, 1], [2, 1, 1]]) == 2
    return fs


def system_check(faces, step):
    child, labels = expand(faces, step)
    n = certify(child)
    u, v, x, y, p, q, r, s = labels
    old_es, new_es = edges(faces), edges(child)
    e, f = edge(u, v), edge(x, y)
    reduced = tuple(z for z in old_es if z not in (e, f))
    hs, chs = cycles(old_es), cycles(new_es)
    assert hs == cycles_dfs(old_es)
    assert chs == cycles_dfs(new_es)
    groups = {name: [] for name in ("N00", "N10", "N01", "N11")}
    for h in hs:
        H = set(selected(old_es, h))
        groups["N"+str(int(e in H))+str(int(f in H))].append(h)
    # Test symbolic equalities using full incidence-vector comparisons.
    def ext(eset, added):
        return sum(1 << i for i, z in enumerate(new_es) if z in eset | set(added))
    arm = [edge(u, p), edge(v, q), edge(x, r), edge(y, s)]
    a, b, c, dd = edge(p, q), edge(r, s), edge(p, r), edge(q, s)
    expected = {}
    for tag in ("N10", "N01", "N11"):
        actual = []
        for h in groups[tag]:
            exterior = set(selected(old_es, h))-{e, f}
            added = ([arm[0], arm[1], c, b, dd] if tag == "N10" else
                     [arm[2], arm[3], c, a, dd] if tag == "N01" else arm+[a, b])
            actual.append(ext(exterior, added))
        expected[tag] = tuple(sorted(actual))
    pa, pb = paths(reduced, u, x), paths(reduced, v, y)
    expected["Pux"] = tuple(sorted(ext(set(selected(reduced, P)),
                                     [arm[0], arm[2], a, dd, b]) for P in pa))
    expected["Pvy"] = tuple(sorted(ext(set(selected(reduced, P)),
                                     [arm[1], arm[3], a, c, b]) for P in pb))
    # D11: all 2-factors of parent with exactly two components, e,f separate.
    ds = []
    full = (1 << len(old_es))-1
    for m in matchings(old_es):
        F = set(selected(old_es, full ^ m))
        if e in F and f in F and not connected(tuple(F)):
            ex = tuple(sorted(F-{e, f}))
            nb = adjacency(ex)
            seen = {u}
            todo = [u]
            for z in todo:
                for w in nb.get(z, ()):
                    if w not in seen:
                        seen.add(w)
                        todo.append(w)
            other = set(adjacency(old_es))-seen
            if v in seen and x in other and y in other and connected(ex, other):
                ds.append(sum(1 << i for i, z in enumerate(reduced) if z in ex))
    expected["D11"] = tuple(sorted(ext(set(selected(reduced, P)), arm+[c, dd]) for P in ds))
    flat = [h for part in expected.values() for h in part]
    assert len(flat) == len(set(flat)) and tuple(sorted(flat)) == chs
    # Arbitrary signed weights test every coefficient formula, not constancy.
    weights = {z: (i*i*7+3*i+11) % 31-15 for i, z in enumerate(new_es)}
    aw, bw, cw, dw = (weights[z] for z in (a, b, c, dd))
    t = [weights[z] for z in arm]
    S = aw+bw+cw+dw
    W = {z: weights[z] for z in reduced}
    W[e], W[f] = t[0]+t[1]-aw, t[2]+t[3]-bw
    for tag in ("N10", "N01", "N11"):
        source_values = sorted(sum(W[z] for z in selected(old_es, h))+
                               (S if tag != "N11" else 2*(aw+bw)) for h in groups[tag])
        target_values = sorted(sum(weights[z] for z in selected(new_es, h)) for h in expected[tag])
        assert source_values == target_values
    for tag, masks, extra in [("Pux", pa, t[0]+t[2]+S-cw),
                              ("Pvy", pb, t[1]+t[3]+S-dw),
                              ("D11", ds, sum(t)+cw+dw)]:
        assert sorted(sum(weights[z] for z in selected(reduced, h))+extra for h in masks) == \
               sorted(sum(weights[z] for z in selected(new_es, h)) for h in expected[tag])
    survivors = tuple(h for tag in ("N10", "N01", "N11") for h in groups[tag])
    path_rank = rank(differences(pa, len(reduced)))
    # Within-class path differences all lie in ker of K's degree matrix.
    joint_rank = rank(differences(pa, len(reduced))+
                      differences(pb, len(reduced))+differences(ds, len(reduced)))
    return {"parent_n": n-4, "step": list(step), "d_parent": dimension(old_es, hs),
            "d_child": dimension(new_es, chs), "d_survival": dimension(old_es, survivors),
            "counts": {**{tag: len(val) for tag, val in groups.items()},
                       "Pux": len(pa), "Pvy": len(pb), "D11": len(ds)},
            "path_rank": path_rank, "joint_within_path_rank": joint_rank,
            "K_cycle_dimension": len(reduced)-len(adjacency(old_es))+1}


def original_system_counterexample(faces):
    child, labels = expand(faces, (0, 0, 2))
    u, v, x, y, p, q, r, s = labels
    es, ce = edges(faces), edges(child)
    e, f = edge(u, v), edge(x, y)
    w = {z: int(p in z) for z in ce}
    assert {sum(w[z] for z in selected(ce, h)) for h in cycles(ce)} == {2}
    aggregate = {z: w[z] for z in es if z not in (e, f)}
    aggregate[e] = sum(w[edge(a, b)] for a, b in ((u, p), (p, q), (q, v)))
    aggregate[f] = sum(w[edge(a, b)] for a, b in ((x, r), (r, s), (s, y)))
    values = {}
    for h in cycles(es):
        H = set(selected(es, h))
        tag = "N"+str(int(e in H))+str(int(f in H))
        values.setdefault(tag, set()).add(sum(aggregate[z] for z in H))
    assert values["N10"] == {2} and values["N01"] == {0}
    # Negative single-path affine-full certificate: explicit unit weighting.
    reduced = tuple(z for z in es if z not in (e, f))
    pa = paths(reduced, u, x)
    assert len(pa) == 1 and rank(differences(pa, len(reduced))) == 0
    return {"parent_faces": faces, "child_faces": child, "labels": list(labels),
            "weight": "alpha_p=1, all other vertex potentials zero",
            "child_constant": 2, "delta": 0,
            "original_aggregated_values": {tag: sorted(val) for tag, val in values.items()},
            "K_edges": reduced, "Pux_paths": [selected(reduced, z) for z in pa],
            "Pux_rank": 0, "K_cycle_dimension": 3}


def run():
    cube = cube_anchor()
    raw = load("bracegen-graphs.json")
    census = list(raw["bfs"].values())
    own = {r["canon"]: canon(r["faces"]) for r in census}
    assert len(set(own.values())) == 15
    # Full metadata consistency, without claiming a replay of the large campaign.
    d1, d2 = load("diag-01.json")["records"], load("diag-02.json")["records"]
    records = d1+d2
    assert len(records) == 452 and len({r["canon"] for r in records}) == 443
    assert all(r["d"] == r["n"]//2+1 and r["enumeration_exhausted"] for r in records)
    by_order = {n: [r for r in census if r["n"] == n] for n in range(8, 21, 2)}
    assert [len(by_order[n]) for n in range(8, 21, 2)] == [1, 0, 1, 1, 2, 2, 8]
    checked = []
    data = {}
    for rec in census:
        es = edges(rec["faces"])
        d = diagnose(rec["faces"])
        expected = next(r for r in d1 if r["canon"] == rec["canon"] and r["group"] == "bfs")
        for key in ("n", "h", "d", "brace"):
            assert d[key] == expected[key]
        cut = nontrivial_cut(es)
        assert d["brace"] == (cut is None)
        sr, count = switch_rank(es, cycles(es))
        checked.append({**d, "history": rec["history"], "switch_rank": sr,
                        "single_switch_pairs": count, "three_cut": cut})
        data[rec["canon"]] = d
    # Exhaustive one-step closure and rooted DAG under both HMM expansions.
    dag = []
    for rec in census:
        if rec["n"]+4 <= 20:
            for st in steps(rec["faces"]):
                fs, _ = expand(rec["faces"], st)
                certify(fs)
                cc = canon(fs)
                targets = [r for r in by_order[rec["n"]+4] if own[r["canon"]] == cc]
                assert len(targets) == 1
                dag.append((rec["canon"], targets[0]["canon"], "C4"))
        if rec["n"]+6 <= 20:
            ce = edges(cube)
            for v in adjacency(edges(rec["faces"])):
                se = splice_edges(edges(rec["faces"]), v, ce, 0, sorted(adjacency(ce)[0]))
                targets = [r for r in by_order[rec["n"]+6] if isomorphic(se, edges(r["faces"]))]
                assert len(targets) == 1
                dag.append((rec["canon"], targets[0]["canon"], "cube"))
    reach = {census[0]["canon"]}
    brace_reach = set(reach)
    for _ in range(15):
        for p, c, kind in dag:
            if p in reach:
                reach.add(c)
            if p in brace_reach and kind == "C4" and data[c]["brace"]:
                brace_reach.add(c)
    assert len(reach) == 15
    missing = [r for r in census if data[r["canon"]]["brace"] and r["canon"] not in brace_reach]
    assert len(missing) == 1 and missing[0]["n"] == 18
    b18 = missing[0]
    contractions = []
    for fi, face in enumerate(b18["faces"]):
        if len(face) == 4:
            for flip in (False, True):
                se = contract_square(edges(b18["faces"]), face, flip)
                row = {"face": fi, "flip": flip, "valid": se is not None}
                if se is not None:
                    assert isomorphic(se, edges(by_order[14][0]["faces"]))
                    row.update({"n": 14, "brace": brace(se), "three_cut": nontrivial_cut(se)})
                    assert not row["brace"]
                contractions.append(row)
    assert len(contractions) == 12
    # All 636 face-labelled expansions from the full order-20 census.
    expansion = []
    original_rows = {(r["parent"], tuple(r["step"])): r for r in load("survival-01.json")["rows"]}
    for rec in census:
        for st in steps(rec["faces"]):
            row = system_check(rec["faces"], st)
            row["parent_history"] = rec["history"]
            if rec["n"] <= 16:
                old = original_rows[rec["canon"], st]
                assert (row["d_parent"], row["d_child"], row["counts"]["N00"]) == \
                       (old["d_parent"], old["d_child"], old["n00"])
                assert (row["d_survival"] == row["d_parent"]) == old["survives"]
            expansion.append(row)
    assert len(expansion) == 636
    small = [r for r in expansion if r["parent_n"] <= 16]
    assert len(small) == 142
    assert sum(r["d_survival"] < r["d_parent"] for r in small) == 136
    # Reconstruct exactly the 240 original splices; all six port maps planar:
    # the pieces may be reflected independently.
    pool = sorted(census, key=lambda r: r["n"])[:8]
    splices = []
    for i, j in [(0, 0), (0, 1), (0, 2), (1, 1), (0, 3), (2, 2),
                 (1, 2), (0, 4), (1, 3), (2, 3)]:
        a, b = edges(pool[i]["faces"]), edges(pool[j]["faces"])
        av, bv = sorted(adjacency(a)), sorted(adjacency(b))
        for v in (av[0], av[len(av)//2]):
            for w in (bv[0], bv[-1]):
                for perm in itertools.permutations(sorted(adjacency(b)[w])):
                    se = splice_edges(a, v, b, w, perm)
                    predicted = 0
                    for omitted, image in zip(sorted(adjacency(a)[v]), perm):
                        aa = sum(not (h >> a.index(edge(v, omitted)) & 1) for h in cycles(a))
                        bb = sum(not (h >> b.index(edge(w, image)) & 1) for h in cycles(b))
                        predicted += aa*bb
                    actual = len(cycles(se))
                    d = dimension(se)
                    assert cycles(se) == cycles_dfs(se)
                    assert actual == predicted and d == dimension(a)+dimension(b)-2
                    splices.append({"pair": [i, j], "ports": [v, w], "n": len(adjacency(se)),
                                    "h": actual, "d": d})
    old = load("as-check-01.json")["checks"]
    assert len(splices) == len(old) == 240
    assert all(all(r[k] == s[k] for k in r) for r, s in zip(splices, old))
    # Deterministic sample: one stored walk graph per order, plus maximum order
    # data reconstructed as adjacency from the literal canonical tuple (no eval).
    large = []
    for n in sorted({r["n"] for r in records if r["n"] > 20}):
        rec = next(r for r in records if r["n"] == n)
        graph = next((r for r in raw["walks"].values() if r["canon"] == rec["canon"]), None)
        if graph:
            es = edges(graph["faces"])
            certify(graph["faces"])
        else:
            adj = ast.literal_eval(rec["canon"])
            es = tuple(sorted({edge(i, j) for i, ns in enumerate(adj) for j in ns}))
            assert all(len(ns) == 3 for ns in adjacency(es).values())
        hs = cycles(es)
        got = {"n": n, "h": len(hs), "d": dimension(es, hs)}
        assert all(got[k] == rec[k] for k in got)
        large.append(got)
    return {"anchors": "PASS", "census": checked, "b18_contractions": contractions,
            "closure_dag_edges": len(dag), "expansions": expansion,
            "splices": splices, "large_sample": large,
            "original_system_counterexample": original_system_counterexample(cube),
            "summary": {"records_metadata_checked": 452, "distinct_metadata": 443,
                        "census_independently_enumerated": 15, "expansion_steps": 636,
                        "small_survival_failures": 136,
                        "max_small_survival_deficit": max(r["d_parent"]-r["d_survival"] for r in small),
                        "exchange_failures": sum(r["d_child"] < r["d_parent"]+2 for r in expansion),
                        "path_full": sum(r["path_rank"] == r["K_cycle_dimension"] for r in expansion),
                        "joint_path_full": sum(r["joint_within_path_rank"] == r["K_cycle_dimension"] for r in expansion),
                        "splices": len(splices), "large_sample": len(large)}}


if __name__ == "__main__":
    print(json.dumps(run(), indent=2))
