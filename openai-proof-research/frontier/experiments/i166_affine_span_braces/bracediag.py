"""Affine-span diagnostics on the generated brace/class sample.

For every generated graph (brace or not), compute:
  * h (two independent enumerators, set equality enforced; visit cap ->
    honest INCOMPLETE record, never a pass),
  * the exact rational affine rank d of Hamiltonian-cycle incidence
    vectors, compared with the full value n/2+1,
  * the Q164 margin h - (n/2+2),
  * whether facial circulations lie in the Hamiltonian-difference span
    (only computed when d is not already full),
  * per-face switch data: does some Hamiltonian cycle alternate on the
    face, and does toggling it stay Hamiltonian (a one-switch witness
    H, H' with H delta H' = the face boundary).

Output: diag-01.json with per-graph records and an aggregate summary.
"""
import json
import runpy
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
L = runpy.run_path(str(HERE / "lib166.py"))

VISIT_CAP = 4_000_000


def face_switch_data(faces, es, hs):
    """Per face: alternating Hamiltonian cycles and connected toggles."""
    out = {"switchable": 0, "alternating_only": 0, "non_alternating": 0,
           "details": []}
    verts = sorted(L["neighbor_map"](es))
    for f in faces:
        fes = [L["ue"](a, b) for a, b in zip(f, f[1:] + f[:1])]
        alt = False
        switch = False
        for h in hs:
            parity = [e in h for e in fes]
            if all(parity[k] != parity[k + 1] for k in range(len(parity) - 1)) \
                    and parity[0] != parity[-1]:
                alt = True
                toggled = h ^ frozenset(fes)
                if len(L["components_of"](verts, sorted(toggled))) == 1:
                    switch = True
                    break
        if switch:
            out["switchable"] += 1
        elif alt:
            out["alternating_only"] += 1
        else:
            out["non_alternating"] += 1
        out["details"].append({"face": f, "alternating": alt,
                               "switchable": switch})
    return out


def diagnose(rec, want_faces=True):
    faces = rec["faces"]
    es = L["face_edges"](faces)
    n = len(L["neighbor_map"](es))
    brace, _ = L["is_brace"](es)
    cut = L["has_nontrivial_3cut"](es)
    assert brace == (not cut), "brace characterisations disagree"
    hs, done = L["hamilton_cycles_dfs"](es, visit_cap=VISIT_CAP)
    out = {"n": n, "canon": rec["canon"], "history": rec["history"],
           "brace": brace, "enumeration_exhausted": done}
    if not done:
        out["status"] = "INCOMPLETE (visit cap); not evidence"
        return out
    check = L["hamilton_cycles_matching"](es)
    assert check == hs, "independent enumerators disagree"
    out["h"] = len(hs)
    out["q164_bound"] = n // 2 + 2
    out["q164_margin"] = len(hs) - (n // 2 + 2)
    full = n // 2 + 1
    d = L["rank_rows"](L["cycle_differences"](es, hs), early_stop=full)
    out["d"] = d
    out["d_full"] = d == full
    if not d == full:
        # identify the missing directions: joint rank with all facial
        # circulations tells whether faces suffice to span the kernel
        frows = [L["face_circulation"](f, es) for f in faces]
        joint = L["rank_rows"](list(L["cycle_differences"](es, hs)) + frows)
        out["joint_rank_with_faces"] = joint
    if want_faces and len(hs) <= 6000:
        sw = face_switch_data(faces, es, hs)
        out["faces_switchable"] = sw["switchable"]
        out["faces_alternating_only"] = sw["alternating_only"]
        out["faces_non_alternating"] = sw["non_alternating"]
    return out


def run():
    graphs = json.loads((HERE / "bracegen-graphs.json").read_text())
    records = []
    todos = []
    for group in ("bfs", "walks"):
        for canon, rec in graphs[group].items():
            rec = dict(rec)
            rec["canon"] = canon
            rec["group"] = group
            todos.append(rec)
    todos.sort(key=lambda r: (r["n"], r["canon"]))
    for k, rec in enumerate(todos):
        out = diagnose(rec)
        out["group"] = rec["group"]
        records.append(out)
        if (k + 1) % 25 == 0:
            print(f"...{k+1}/{len(todos)}", file=sys.stderr, flush=True)
    done = [r for r in records if r.get("enumeration_exhausted")]
    braces = [r for r in done if r["brace"]]
    summary = {
        "graphs_total": len(records),
        "enumerations_exhausted": len(done),
        "incomplete": len(records) - len(done),
        "braces_exhausted": len(braces),
        "braces_d_full": sum(1 for r in braces if r["d_full"]),
        "braces_d_not_full": [r["canon"] for r in braces if not r["d_full"]],
        "braces_q164_violations": [r["canon"] for r in braces
                                   if r["q164_margin"] < 0],
        "all_members_q164_violations": [r["canon"] for r in done
                                        if r["q164_margin"] < 0],
        "members_d_not_full": [r["canon"] for r in done if not r["d_full"]],
        "face_switch_totals": {
            "switchable": sum(r.get("faces_switchable", 0) for r in braces),
            "alternating_only": sum(r.get("faces_alternating_only", 0)
                                    for r in braces),
            "non_alternating": sum(r.get("faces_non_alternating", 0)
                                   for r in braces)},
    }
    return {"summary": summary, "records": records}


if __name__ == "__main__":
    result = run()
    (HERE / "diag-01.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result["summary"], indent=2))
