"""Exact affine ranks and explicit failed facial-toggle witnesses."""
import json
import runpy
from fractions import Fraction
from pathlib import Path

g = runpy.run_path(str(Path(__file__).with_name("graphs.py")))


def affine_rank(es, cycles):
    cycles = sorted(cycles, key=lambda h: sorted(h))
    base = cycles[0]
    rows = {}
    pivots = []
    for index, h in enumerate(cycles[1:], 1):
        row = [Fraction(int(e in h)-int(e in base)) for e in es]
        for pivot, old in sorted(rows.items()):
            if row[pivot]:
                a = row[pivot]
                row = [x-a*y for x, y in zip(row, old)]
        if any(row):
            pivot = next(j for j, x in enumerate(row) if x)
            a = row[pivot]
            rows[pivot] = [x/a for x in row]
            pivots.append(index)
    return {"rank": len(rows), "cycle_basis_indices": [0]+pivots}


def components(vertices, es):
    adj = g["adjacency"](es)
    unseen = set(vertices)
    out = []
    while unseen:
        seen = {min(unseen)}
        stack = list(seen)
        while stack:
            for w in adj.get(stack.pop(), []):
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        unseen -= seen
        out.append(sorted(seen))
    return out


def run(decisive):
    ranks = []
    for key, cycle_key in (("certificate", "old_cycles"),
                           ("expanded_certificate", "new_cycles")):
        cert = decisive[key]
        hs = {frozenset(map(tuple, h)) for h in decisive[cycle_key]}
        rank = affine_rank(list(map(tuple, cert["edges"])), hs)
        assert rank["rank"] == cert["n"]//2+1
        ranks.append({"n": cert["n"], "h": len(hs), **rank})
    piece_ranks = []
    for faces in (decisive["base_certificate"]["faces"],
                  decisive["base_expanded_certificate"]["faces"], g["prism"](10)):
        es = g["edges"](faces)
        hs = g["pruned_paths"](es, min(g["adjacency"](es)))
        n = len(g["adjacency"](es))
        rank = affine_rank(es, hs)
        assert rank["rank"] == n//2+1
        piece_ranks.append({"n": n, "h": len(hs), **rank})
    faces = g["prism"](8)
    f = faces[1]
    step = (1, 3, 7)
    _, (u, v, x, y) = g["square"](faces, step)
    es = g["edges"](faces)
    hs = g["dfs_cycles"](es)
    assert hs == g["pruned_paths"](es, 0)
    lost = [h for h in hs if g["edge"](u, v) not in h and g["edge"](x, y) not in h]
    assert len(lost) == 1
    h = lost[0]
    toggles = []
    for arc in (f[8:]+f[:4], f[4:8]):
        toggled = h ^ {g["edge"](a, b) for a, b in zip(arc, arc[1:])}
        comps = components(range(16), toggled)
        assert len(comps) == 2
        assert sorted(len(g["adjacency"](toggled)[v]) for v in range(16)) == [1, 1]+[2]*14
        toggles.append({"arc": arc, "output_edges": [list(e) for e in sorted(toggled)],
                        "components": comps})
    # Independent unpruned/pruned comparisons at small orders.
    short = []
    for m in (4, 6, 8, 10):
        faces = g["prism"](m)
        es = g["edges"](faces)
        hs = g["dfs_cycles"](es)
        assert hs == g["pruned_paths"](es, 0)
        assert len(hs) == m+2
        for step in g["steps"](faces):
            fi, i, j = step
            if j-i != 2 and len(faces[fi])-(j-i) != 2:
                continue
            _, (u, v, x, y) = g["square"](faces, step)
            e, f = g["edge"](u, v), g["edge"](x, y)
            lost = {h for h in hs if e not in h and f not in h}
            k = [z for z in es if z not in (e, f)]
            a, b = (u, x) if g["edge"](u, x) in k else (v, y)
            paths = g["pruned_paths"](k, a, b)
            assert paths == g["dfs_paths"](k, a, b)
            assert paths == {h-{g["edge"](a, b)} for h in lost}
            short.append({"m": m, "step": list(step), "lost": len(lost)})
    return {"counterexample_affine_ranks": ranks, "splice_piece_affine_ranks": piece_ranks,
            "facial_toggle_failure": {"prism_m": 8, "step": list((1, 3, 7)),
                                      "cycle": [list(e) for e in sorted(h)],
                                      "toggles": toggles},
            "short_side_bijections": short}


if __name__ == "__main__":
    d = json.loads(Path(__file__).with_name("decisive-02.json").read_text())
    print(json.dumps(run(d), indent=2))
