"""Brace and class-member generation for the I166 affine-span attack.

Phase 1: BFS from the cube over ALL simple cubic bipartite planar
3-connected graphs (class members) by square (C4) and cube expansions,
up to a fixed order, deduplicated by canonical form.  HMM Theorem 4 (GSW
Theorem 5.1) states every class member arises this way.

Phase 2: seeded pseudo-random expansion walks that keep only braces,
producing larger braces of varied construction history.

Every graph record carries its full oriented face list; class membership
is certified by lib166.certify (which performs all deletion checks), and
the brace flag is computed two independent ways (2-extendability and the
contraction-based nontrivial-3-cut screen), with agreement enforced.
"""
import json
import random
import runpy
from pathlib import Path

L = runpy.run_path(str(Path(__file__).with_name("lib166.py")))


def record(faces, history):
    cert = L["certify"](faces)
    es = L["face_edges"](faces)
    canon = L["canonical_form"](faces)
    return {"n": cert["n"], "faces": faces, "canon": repr(canon),
            "history": history, "edges": es}


def brace_flags(es):
    brace, _ = L["is_brace"](es)
    cut = L["has_nontrivial_3cut"](es)
    assert brace == (not cut), "brace characterisations disagree"
    return brace


def bfs_clean(max_order=20):
    """Exhaustive BFS; returns (by_order, dag_edges, cube_canon).

    dag_edges lists (parent_canon, child_canon, op) for EVERY generated
    expansion, so brace-only reachability can be computed over the full
    expansion DAG rather than a first-discovery spanning tree.
    """
    cube = L["cube_faces"]()
    first = record(cube, "cube")
    by_order = {8: {first["canon"]: first}}
    seen = {first["canon"]}
    dag = []
    for order in range(8, max_order, 2):
        for rec in list(by_order.get(order, {}).values()):
            faces = rec["faces"]
            pcanon = rec["canon"]
            children = []
            for step in L["admissible_steps"](faces):
                child, _ = L["square_expand"](faces, *step)
                children.append((child, rec["history"] + f" S{list(step)}",
                                 "S"))
            for vtx in sorted(L["neighbor_map"](L["face_edges"](faces))):
                child = L["cube_expand_vertex"](faces, vtx)
                children.append((child, rec["history"] + f" C{vtx}", "C"))
            for child, hist, op in children:
                es = L["face_edges"](child)
                if len(L["neighbor_map"](es)) > max_order:
                    continue
                c = repr(L["canonical_form"](child))
                dag.append((pcanon, c, op))
                if c in seen:
                    continue
                seen.add(c)
                r = record(child, hist)
                by_order.setdefault(r["n"], {})[c] = r
    return by_order, dag, first["canon"]


def random_walks(seeds_per_start=8, levels=9, keep_per_order=60,
                 master_seed=166):
    """Seeded expansion walks keeping braces only, from cube and prisms."""
    rng = random.Random(master_seed)
    found = {}
    starts = [("cube", L["cube_faces"]())] + [
        (f"prism{m}", L["prism_faces"](m)) for m in (6, 8, 10, 12, 14)]
    for name, faces0 in starts:
        for s in range(seeds_per_start):
            faces = faces0
            hist = f"{name}/s{s}"
            for level in range(levels):
                steps = list(L["admissible_steps"](faces))
                rng.shuffle(steps)
                brace_child = None
                for step in steps[:60]:
                    child, _ = L["square_expand"](faces, *step)
                    es = L["face_edges"](child)
                    if len(L["neighbor_map"](es)) > 48:
                        continue
                    if brace_flags(es):
                        brace_child = (child, es, step)
                        break
                if brace_child is None:
                    break
                faces, es, step = brace_child
                hist += f" S{list(step)}"
                c = repr(L["canonical_form"](child))
                n = len(L["neighbor_map"](es))
                per_order = [k for k, v in found.items() if v["n"] == n]
                if c not in found and len(per_order) < keep_per_order:
                    found[c] = {"n": n, "faces": faces, "canon": c,
                                "history": hist, "edges": es}
    return found


def run(quick=False):
    max_order = 16 if quick else 20
    by_order, dag, cube_canon = bfs_clean(max_order)
    counts = {n: len(layer) for n, layer in sorted(by_order.items())}
    brace_of = {}
    for order in sorted(by_order):
        for c, rec in sorted(by_order[order].items()):
            brace_of[c] = brace_flags(rec["edges"])
    # brace-only reachability through square (C4) steps over the full DAG
    reachable = {cube_canon}
    changed = True
    while changed:
        changed = False
        for p, c, op in dag:
            if op == "S" and p in reachable and c not in reachable \
                    and brace_of.get(c):
                reachable.add(c)
                changed = True
    unreachable_braces = [c for order in by_order.values() for c in order
                          if brace_of[c] and c not in reachable]
    meta = []
    for order in sorted(by_order):
        for c, rec in sorted(by_order[order].items()):
            meta.append({"n": rec["n"], "canon": c, "brace": brace_of[c],
                         "brace_C4_reachable": c in reachable,
                         "history": rec["history"]})
    walks = {} if quick else random_walks()
    result = {"counts_by_order": counts, "class_members": meta,
              "brace_count_by_order": {
                  n: sum(1 for c in layer if brace_of[c])
                  for n, layer in sorted(by_order.items())},
              "unreachable_braces_via_brace_C4": len(unreachable_braces),
              "random_braces_found": len(walks)}
    graphs = {"bfs": {c: rec for order in by_order.values()
                      for c, rec in order.items()},
              "walks": walks}
    return result, graphs


if __name__ == "__main__":
    import sys
    quick = "--quick" in sys.argv
    result, graphs = run(quick)
    Path("bracegen-graphs.json").write_text(json.dumps(graphs))
    if not quick:
        Path("bracegen-meta.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result, indent=2))
