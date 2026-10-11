"""Direct numerical checks of I165's AS (affine splice) interface.

For small generated class members G1, G2 (braces or not) and a spread of
port vertices, splice them and verify independently:

  (count)  h(G) = sum_i a_i b_i     -- I165's exact splice count formula
  (AS)     d(G) = d(G1) + d(G2) - 2 -- affine-rank additivity

where a_i, b_i are the port pair counts at the two ports under the
cyclic alignment used by the splice, all ranks exact over Q and all
cycle sets cross-validated by two independent enumerators.
"""
import itertools
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
L = runpy.run_path(str(HERE / "lib166.py"))


def port_counts(hs, es, v):
    """Counts of Hamiltonian cycles by which pair of edges at v they use."""
    nbv = sorted(L["neighbor_map"](es)[v])
    counts = []
    for a, b in itertools.combinations(nbv, 2):
        pair = frozenset((L["ue"](v, a), L["ue"](v, b)))
        counts.append(sum(1 for h in hs if pair <= h))
    return nbv, counts


def all_port_maps(nbv1, nbv2):
    """All six bijections nb(v1) -> nb(v2); exactly the orientation-
    consistent ones yield splices that pass certification (checked)."""
    return [dict(zip(nbv1, perm)) for perm in itertools.permutations(nbv2)]


def check_splice(faces1, v1, faces2, v2, pm):
    try:
        g, _ = L["splice_faces"](faces1, v1, faces2, v2, pm)
        cert = L["certify"](g)  # full deletion checks
    except AssertionError:
        return None  # orientation-inconsistent port map: not a sphere
    es = L["face_edges"](g)
    hs, done = L["hamilton_cycles_dfs"](es, visit_cap=6_000_000)
    assert done
    assert L["hamilton_cycles_matching"](es) == hs
    n = len(L["neighbor_map"](es))
    d = L["rank_rows"](L["cycle_differences"](es, hs), early_stop=n // 2 + 1)
    return cert, hs, d


def run():
    graphs = json.loads((HERE / "bracegen-graphs.json").read_text())
    pool = sorted(graphs["bfs"].values(), key=lambda r: r["n"])[:8]
    specs = []
    for rec in pool:
        faces = [list(f) for f in rec["faces"]]
        es = L["face_edges"](faces)
        hs, done = L["hamilton_cycles_dfs"](es)
        assert done
        assert L["hamilton_cycles_matching"](es) == hs
        n = rec["n"]
        d = L["rank_rows"](L["cycle_differences"](es, hs),
                           early_stop=n // 2 + 1)
        specs.append({"faces": faces, "edges": es, "n": n, "h": len(hs),
                      "d": d, "hs": hs, "history": rec["history"],
                      "brace": rec.get("brace")})
    checks = []
    rng_order = [(0, 0), (0, 1), (0, 2), (1, 1), (0, 3), (2, 2),
                 (1, 2), (0, 4), (1, 3), (2, 3)]
    for i, j in rng_order:
        if i >= len(specs) or j >= len(specs):
            continue
        g1, g2 = specs[i], specs[j]
        nb1 = L["neighbor_map"](g1["edges"])
        nb2 = L["neighbor_map"](g2["edges"])
        verts1 = sorted(nb1)
        verts2 = sorted(nb2)
        picks1 = [verts1[0], verts1[len(verts1) // 2]]
        picks2 = [verts2[0], verts2[-1]]
        for v1 in picks1:
            for v2 in picks2:
                nbv1, a = port_counts(g1["hs"], g1["edges"], v1)
                nbv2 = sorted(nb2[v2])
                valid = 0
                for pm in all_port_maps(nbv1, nbv2):
                    # b aligned with a through the port map
                    b = []
                    for x, y in itertools.combinations(nbv1, 2):
                        pair = frozenset((L["ue"](v2, pm[x]),
                                          L["ue"](v2, pm[y])))
                        b.append(sum(1 for h in g2["hs"] if pair <= h))
                    predicted = sum(x * y for x, y in zip(a, b))
                    got = check_splice(g1["faces"], v1,
                                       g2["faces"], v2, pm)
                    if got is None:
                        continue
                    valid += 1
                    cert, hs, d = got
                    n = cert["n"]
                    ok_count = len(hs) == predicted
                    ok_as = d == g1["d"] + g2["d"] - 2
                    checks.append({
                        "pair": [i, j], "ports": [v1, v2],
                        "n": n, "h": len(hs), "h_predicted": predicted,
                        "count_ok": ok_count, "d": d,
                        "d_predicted": g1["d"] + g2["d"] - 2,
                        "as_ok": ok_as,
                        "d_full": d == n // 2 + 1})
                    assert ok_count, "splice count formula failed"
                    assert ok_as, "AS affine formula failed"
                assert valid in (3, 6), f"unexpected valid maps: {valid}"
    summary = {"splices_checked": len(checks),
               "count_formula_failures": sum(1 for c in checks
                                             if not c["count_ok"]),
               "as_failures": sum(1 for c in checks if not c["as_ok"]),
               "all_d_full": all(c["d_full"] for c in checks),
               "status": "PASS"}
    return {"summary": summary, "checks": checks}


if __name__ == "__main__":
    result = run()
    (HERE / "as-check-01.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result["summary"], indent=2))
