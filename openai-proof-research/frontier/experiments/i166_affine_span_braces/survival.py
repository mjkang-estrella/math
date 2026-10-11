"""Affine-survival audit for square (C4) expansions.

I165 refuted the counting form of expansion monotonicity: cycles avoiding
both expansion edges (class N00) can be numerous (138/576) yet all are
destroyed.  The affine question is weaker and is what the AE lemma needs:

  (SURV)  every Hamiltonian cycle of G avoiding both expansion edges
          already lies in the affine hull of the cycles using e or f;

equivalently rank(differences of N10 u N01 u N11) == d(G).

For every generated graph of order <= 16 and every admissible step, we
compute both sides exactly (two independent enumerators, rational rank)
plus d(H) for the expanded child H, and record whether the affine
exchange inequality d(H) >= d(G) + 2 holds.  Output: survival-01.json.
"""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
L = runpy.run_path(str(HERE / "lib166.py"))


def class_ranks(faces, step):
    es = L["face_edges"](faces)
    n = len(L["neighbor_map"](es))
    fi, i, j = step
    f = faces[fi]
    u, v, x, y = f[i], f[i + 1], f[j], f[(j + 1) % len(f)]
    e = L["ue"](u, v)
    g = L["ue"](x, y)
    hs, done = L["hamilton_cycles_dfs"](es)
    assert done
    assert L["hamilton_cycles_matching"](es) == hs
    n00 = [h for h in hs if e not in h and g not in h]
    rest = [h for h in hs if e in h or g in h]
    d_all = L["rank_rows"](L["cycle_differences"](es, hs),
                           early_stop=n // 2 + 1)
    d_rest = L["rank_rows"](L["cycle_differences"](es, rest),
                            early_stop=n // 2 + 1)
    return {"n00": len(n00), "rest": len(rest), "d_all": d_all,
            "d_rest": d_rest, "survives": d_rest == d_all}


def run():
    graphs = json.loads((HERE / "bracegen-graphs.json").read_text())
    small = [r for r in graphs["bfs"].values() if r["n"] <= 16]
    small.sort(key=lambda r: (r["n"], r["canon"]))
    rows = []
    worst_deficit = 0
    for rec in small:
        faces = [list(f) for f in rec["faces"]]
        es = L["face_edges"](faces)
        n = rec["n"]
        hs_all = None
        for step in L["admissible_steps"](faces):
            cr = class_ranks(faces, step)
            child, _ = L["square_expand"](faces, *step)
            ces = L["face_edges"](child)
            cn = len(L["neighbor_map"](ces))
            chs, done = L["hamilton_cycles_dfs"](ces)
            assert done
            assert L["hamilton_cycles_matching"](ces) == chs
            d_child = L["rank_rows"](L["cycle_differences"](ces, chs),
                                     early_stop=cn // 2 + 1)
            ae_holds = d_child >= cr["d_all"] + 2
            rows.append({"parent": rec["canon"], "n_parent": n,
                         "step": list(step),
                         "d_parent": cr["d_all"], "d_child": d_child,
                         "n00": cr["n00"], "rest": cr["rest"],
                         "survives": cr["survives"],
                         "ae_holds": ae_holds,
                         "d_child_full": d_child == cn // 2 + 1})
            worst_deficit = max(worst_deficit,
                                cr["d_all"] - cr["d_rest"])
    summary = {"steps_checked": len(rows),
               "survival_failures": [r for r in rows if not r["survives"]],
               "ae_failures": [r for r in rows if not r["ae_holds"]],
               "d_child_not_full": [r for r in rows
                                    if not r["d_child_full"]],
               "worst_deficit": worst_deficit,
               "max_n00_share": max((r["n00"] / (r["n00"] + r["rest"])
                                     for r in rows), default=0),
               "status": "PASS" if all(r["survives"] and r["ae_holds"]
                                       for r in rows) else "FAIL"}
    return {"summary": summary, "rows": rows}


if __name__ == "__main__":
    result = run()
    (HERE / "survival-01.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result["summary"], indent=2)[:2000])
