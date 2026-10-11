"""Independent parent DFS/rational-rank checks, reusing only parent helpers."""
import hashlib
import json
import runpy
from collections import Counter
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i174_prism_gadget_survival"
HELPER = BASE.parent / "i172-parent-certificates.py"
H = runpy.run_path(str(HELPER))
edge, paths, cycles, rank, differences, minus = (
    H[k] for k in ("edge", "paths", "cycles", "rank", "differences", "minus"))


def vec(es, selected):
    return tuple(int(e in selected) for e in es)


def families(record):
    g = record["graph"]
    es = list(map(tuple, g["edges"]))
    vertices = {v for e in es for v in e}
    u, v, x, y = record["uvxy"]
    e, f = edge(u, v), edge(x, y)
    hc = cycles(es, vertices)
    fs = {"N%d%d" % (a, b): sorted(vec(es, c) for c in hc if (e in c, f in c) == (a, b))
          for a in (0, 1) for b in (0, 1)}
    remaining = set(es) - {e, f}
    fs["Pux"] = sorted(vec(es, p) for p in paths(remaining, u, x, vertices))
    fs["Pvy"] = sorted(vec(es, p) for p in paths(remaining, v, y, vertices))
    covers = set()
    for p in paths(remaining, u, v, vertices, spanning=False):
        used = {z for t in p for z in t}
        if x in used or y in used:
            continue
        for q in paths(remaining, x, y, vertices - used):
            covers.add(vec(es, p | q))
    fs["D11"] = sorted(covers)
    assert all(set(rows) == set(map(tuple, record["families"][k])) for k, rows in fs.items())
    S = sorted(fs["N10"] + fs["N01"] + fs["N11"])
    L, V = differences(S), differences(fs["N00"])
    L0 = sum((differences(fs[k]) for k in ("N10", "N01", "N11")), [])
    U = sum((differences(fs[k]) for k in ("Pux", "Pvy", "D11")), [])
    ef = vec(es, {e, f})
    b = tuple(p + q + d + 2*z - 3*c for p, q, d, z, c in
              zip(fs["Pux"][0], fs["Pvy"][0], fs["D11"][0], ef, S[0]))
    assert b == tuple(record["bridge"])
    dg, dl, lu = rank(differences(S + fs["N00"])), rank(L), rank(L + U)
    assert [dg, dl, rank(L0)] == [record["row"][k] for k in ("dg", "rankL", "rankL0")]
    assert [dg - dl, lu - dl, rank(L + U + [b]) - lu] == [record["row"][k] for k in ("ell", "t", "eta")]
    good_directions, residual_directions = [], []
    for k, info in record["residuals"].items():
        q = tuple(info["q"])
        good = [n for n in fs["N00"] if minus(n, q) in fs[k]]
        residual = [p for p in fs[k] if tuple(a+b for a, b in zip(p, q)) not in fs["N00"]]
        assert good == list(map(tuple, info["good"])) and residual == list(map(tuple, info["residual"]))
        anchor = minus(good[0], q) if good else fs[k][0]
        good_directions += differences(good)
        residual_directions += [minus(p, anchor) for p in residual]
    dv = rank(L0 + V) - rank(L0 + good_directions)
    dr = rank(L0 + good_directions + residual_directions) - rank(L0 + good_directions)
    c = tuple(n-a-b+c for n, a, b, c in zip(fs["N00"][0], fs["N10"][0], fs["N01"][0], fs["N11"][0]))
    assert c == tuple(record["c"])
    ep = rank(L0 + V + [c]) - rank(L0 + V)
    assert [dv, dr, ep] == [record["row"][k] for k in ("delta_V", "delta_R", "epsilon")]
    return fs


def check_matchings(record):
    g, certificate = record["graph"], record["brace"]
    es = list(map(tuple, g["edges"]))
    vertices = {v for e in es for v in e}
    expected = {(i, j) for i, j in combinations(range(len(es)), 2) if not set(es[i]) & set(es[j])}
    supplied = set()
    for i, j, indices in certificate["extended_pairs"]:
        assert (i, j) not in supplied and i in indices and j in indices
        assert len(indices) == len(set(indices)) and all(0 <= k < len(es) for k in indices)
        assert Counter(v for k in indices for v in es[k]) == Counter({v: 1 for v in vertices})
        supplied.add((i, j))
    failed = set(map(tuple, certificate["failed_pairs"]))
    assert expected == supplied | failed and not supplied & failed
    proved = set()
    for proof in record["tight_failures"]:
        side = set(proof["side"])
        cut = [i for i, e in enumerate(es) if len(set(e) & side) == 1]
        assert len(cut) == 3 and cut == proof["cut_indices"]
        # Independently solve the bipartition and the imbalance equation.
        colors = {min(vertices): 0}
        while len(colors) != len(vertices):
            previous = len(colors)
            for a, b in es:
                if a in colors and b not in colors:
                    colors[b] = 1 - colors[a]
                if b in colors and a not in colors:
                    colors[a] = 1 - colors[b]
            assert len(colors) > previous
        assert all(colors[a] != colors[b] for a, b in es)
        port_color = colors[next(v for v in es[cut[0]] if v in side)]
        assert all(colors[next(v for v in es[k] if v in side)] == port_color for k in cut)
        assert sum(1 if colors[v] == port_color else -1 for v in side) == 1
        proved.update(combinations(cut, 2))
    assert proved == failed and not certificate["brace"]
    return len(supplied), len(failed)


def main():
    exp = json.loads((BASE / "experiments-attempt-03.json").read_bytes())
    structural = json.loads((BASE / "structural-attempt-03.json").read_bytes())
    assert len(exp["initials"]) == 3 and exp["first_count"] == 6 and exp["second_count"] == 0
    rows, matches, failures = [], 0, 0
    for kind, records in (("initial", exp["initials"]), ("first", exp["first_children"])):
        for r in records:
            families(r)
            a, b = check_matchings(r)
            matches += a
            failures += b
            assert r["row"]["ell"] == (3 if kind == "initial" else 0)
            rows.append(dict(kind=kind, attachments=r["attachments"], order=r["graph"]["n"],
                             cycles=len(r["cycles"]), ell=r["row"]["ell"],
                             rankL=r["row"]["rankL"], matching_witnesses=a, failed_pairs=b))
    applications = []
    for r, a in zip(exp["first_children"], structural["applications"]):
        assert r["history"] == a["history"] and r["attachments"] == a["attachments"]
        small = a["contracted"]
        families(small)
        g, h = r["graph"], small["graph"]
        side = set(r["saturation_decomposition"]["side"])
        es, hes = list(map(tuple, g["edges"])), list(map(tuple, h["edges"]))
        mapping = [None if u in side and v in side else hes.index(edge(7 if u in side else u, 7 if v in side else v))
                   for u, v in es]
        def project(c):
            ans = [0] * len(hes)
            for i, value in zip(mapping, c):
                if i is not None:
                    ans[i] += value
            return tuple(ans)
        for name, family in r["families"].items():
            counts = Counter(map(project, family))
            assert counts == {tuple(z["vector"]): z["count"] for z in a["all_seven_projection"][name]}
            assert set(counts) == set(map(tuple, small["families"][name]))
        survivors = sorted(r["families"]["N10"] + r["families"]["N01"] + r["families"]["N11"])
        fibres = {}
        for c in survivors:
            fibres.setdefault(project(c), []).append(c)
        kernel = sum((differences(f) for f in fibres.values()), [])
        image = differences(sorted(fibres))
        assert all(not any(project(v)) for v in kernel)
        assert rank(kernel) == a["attachment_kernel"] == r["attachments"][1] - 1
        assert rank(image) == small["row"]["rankL"] == len(hes) - h["n"] + 1
        assert rank(kernel) + rank(image) == r["row"]["rankL"]
        cut = [i for i, e in enumerate(hes) if 7 in e]
        assert {tuple(v[i] for i in cut) for v in fibres} == {(0,1,1),(1,0,1),(1,1,0)}
        applications.append(dict(attachments=r["attachments"], history=r["history"],
                                 exterior_order=h["n"], image_rank=rank(image), kernel_rank=rank(kernel)))
    assert matches == 9324 and failures == 36
    result = dict(status="PASS", graphs=rows, structural_applications=applications,
                  complete_seven_family_checks=15, matching_witnesses=matches, tight_cut_failures=failures,
                  method="Parent-only plain DFS and Fraction ranks, exact residual sets, complete seven-class projections and kernel/image ranks",
                  reused_parent_helper=str(HELPER.relative_to(ROOT)),
                  helper_sha256=hashlib.sha256(HELPER.read_bytes()).hexdigest(),
                  child_python_imported=False)
    with (BASE.parent / "i174-parent-certificates.json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: 15 complete seven-family checks, six kernel/image splits, 9324 matchings, 36 tight-cut failures")


if __name__ == "__main__":
    main()
