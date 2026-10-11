"""Second, disjoint brace sample: longer seeded walks (orders up to 64)
from larger prism starts, with a different master seed, each graph fully
diagnosed (two independent enumerators, exact rational affine rank).

Purpose: extend the universal d = n/2 + 1 evidence well past the BFS
horizon and the first walk batch (which stopped at 48).
"""
import json
import random
import runpy
import sys
from pathlib import Path

HERE = Path(__file__).resolve().parent
L = runpy.run_path(str(HERE / "lib166.py"))

MAX_ORDER = 64
VISIT_CAP = 8_000_000


def walk(rng, faces0, hist0, found):
    faces = faces0
    hist = hist0
    while True:
        es = L["face_edges"](faces)
        n = len(L["neighbor_map"](es))
        steps = list(L["admissible_steps"](faces))
        rng.shuffle(steps)
        advanced = False
        for step in steps[:80]:
            child, _ = L["square_expand"](faces, *step)
            ces = L["face_edges"](child)
            cn = len(L["neighbor_map"](ces))
            if cn > MAX_ORDER:
                continue
            brace, _ = L["is_brace"](ces)
            if not brace:
                continue
            faces = child
            hist += f" S{list(step)}"
            c = repr(L["canonical_form"](child))
            per_order = [k for k, v in found.items() if v["n"] == cn]
            if c not in found and len(per_order) < 25:
                found[c] = {"n": cn, "faces": child, "history": hist,
                            "canon": c}
            advanced = True
            break
        if not advanced:
            return


def diagnose(rec):
    faces = rec["faces"]
    es = L["face_edges"](faces)
    n = len(L["neighbor_map"](es))
    hs, done = L["hamilton_cycles_dfs"](es, visit_cap=VISIT_CAP)
    out = {"n": n, "canon": rec["canon"], "history": rec["history"],
           "enumeration_exhausted": done}
    if not done:
        out["status"] = "INCOMPLETE (visit cap); not evidence"
        return out
    assert L["hamilton_cycles_matching"](es) == hs
    out["h"] = len(hs)
    out["q164_margin"] = len(hs) - (n // 2 + 2)
    d = L["rank_rows"](L["cycle_differences"](es, hs),
                       early_stop=n // 2 + 1)
    out["d"] = d
    out["d_full"] = d == n // 2 + 1
    return out


def run():
    rng = random.Random(166002)
    found = {}
    starts = [(f"prism{m}", L["prism_faces"](m))
              for m in (16, 18, 20, 22, 24)]
    for name, faces0 in starts:
        brace, _ = L["is_brace"](L["face_edges"](faces0))
        assert brace
        for s in range(10):
            walk(rng, faces0, f"{name}/t{s}", found)
    records = []
    items = sorted(found.values(), key=lambda r: (r["n"], r["canon"]))
    for k, rec in enumerate(items):
        out = diagnose(rec)
        records.append(out)
        if (k + 1) % 20 == 0:
            print(f"...{k+1}/{len(items)}", file=sys.stderr, flush=True)
    done = [r for r in records if r.get("enumeration_exhausted")]
    summary = {"braces_found": len(found),
               "enumerations_exhausted": len(done),
               "incomplete": len(records) - len(done),
               "d_not_full": [r["canon"] for r in done if not r["d_full"]],
               "q164_violations": [r["canon"] for r in done
                                   if r["q164_margin"] < 0],
               "orders": sorted({r["n"] for r in records}),
               "max_h": max((r.get("h", 0) for r in done), default=0)}
    return {"summary": summary, "records": records}


if __name__ == "__main__":
    result = run()
    (HERE / "diag-02.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result["summary"], indent=2)[:1500])
