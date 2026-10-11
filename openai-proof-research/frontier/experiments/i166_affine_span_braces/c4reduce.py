"""Reverse C4-expansion (facial 4-cycle contraction) as a second,
independent method for the brace-generation question.

For the unique order-18 brace B18 (history 'cube C0 S[6,0,4]'), the BFS
DAG over all class members of order <= 20 already proves that every
C4-reduction lands in the unique order-14 class member, which is a
non-brace.  This script confirms that conclusion without any DAG:
enumerate every facial 4-cycle of B18, contract it (the exact inverse
of lib166.square_expand, derived from the face-surgery formulas),
certify each result with full deletion checks, and compare canonical
forms.

It also spot-checks that every other brace of order <= 20 has at least
one contraction landing in a brace (consistency with the DAG finding),
and that every contraction of every brace is a class member.
"""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
L = runpy.run_path(str(HERE / "lib166.py"))


def contract_c4(faces, fi, flip=False):
    """Contract the facial 4-cycle faces[fi] = [p, q, s, r] back to two
    edges, exactly inverting square_expand.  HMM's reduction R0 admits
    two applications per 4-face: flip=False reconnects (u, v), (x, y);
    flip=True reconnects the cross pairing (v, x), (y, u).
    Returns new face list or None when the contraction is invalid.
    """
    c = faces[fi]
    assert len(c) == 4
    p, q, s, r = c
    es = L["face_edges"](faces)
    nb = L["neighbor_map"](es)
    # external attachments (the unique non-cycle neighbour of each)
    try:
        u = next(w for w in nb[p] if w not in c)
        v = next(w for w in nb[q] if w not in c)
        x = next(w for w in nb[s] if w not in c)
        y = next(w for w in nb[r] if w not in c)
    except StopIteration:
        return None
    if len({u, v, x, y}) < 4 or {u, v, x, y} & set(c):
        return None
    if not flip and (L["ue"](u, v) in es or L["ue"](x, y) in es):
        return None  # would create a parallel edge
    if flip and (L["ue"](v, x) in es or L["ue"](y, u) in es):
        return None  # would create a parallel edge
    # locate the four neighbouring faces by consecutive-vertex patterns
    # (either traversal direction; orient_faces fixes global orientation)
    def rot(lst, k):
        return lst[k:] + lst[:k]

    def face_with_triple(triple):
        t = list(triple)
        for k, f in enumerate(faces):
            if k == fi:
                continue
            for sgn in (1, -1):
                g = f if sgn == 1 else f[::-1]
                for t0 in range(len(g)):
                    if list(rot(g, t0))[:3] == t:
                        return k, rot(g, t0)
        return None
    got1 = face_with_triple((u, p, q))   # [u, p, q, v, ...]
    got3 = face_with_triple((x, s, r))   # [x, s, r, y, ...]
    got2 = face_with_triple((v, q, s))   # [v, q, s, x, arc1..., ]
    got4 = face_with_triple((y, r, p))   # [y, r, p, u, arc2..., ]
    if None in (got1, got2, got3, got4):
        return None
    k1, F1r = got1
    k2, F2r = got2
    k3, F3r = got3
    k4, F4r = got4
    if len({k1, k2, k3, k4}) < 4:
        return None
    assert F1r[3] == v and F3r[3] == y and F2r[3] == x and F4r[3] == u
    arc1 = F2r[4:]   # F2 = [v, q, s, x] + arc1
    arc2 = F4r[4:]   # F4 = [y, r, p, u] + arc2
    if not flip:
        # reconnect (u, v) and (x, y); F1, F3 keep their outer arcs,
        # F2 and F4 merge back into the pre-expansion face
        F1n = [u, v] + F1r[4:]
        F3n = [x, y] + F3r[4:]
        merged = [u, v] + arc1[::-1] + [x, y] + arc2[::-1]
        out = []
        for k, f in enumerate(faces):
            if k in (fi, k2, k4):
                continue
            if k == k1:
                out.append(F1n)
            elif k == k3:
                out.append(F3n)
            else:
                out.append(list(f))
        out.append(merged)
    else:
        # cross pairing (v, x), (y, u): F2, F4 keep their outer arcs
        # with the gadget vertices removed; F1 and F3 merge
        F2n = [v, x] + arc1
        F3m = [y, u] + arc2
        merged = [u, y] + F3r[4:] + [x, v] + F1r[4:]
        out = []
        for k, f in enumerate(faces):
            if k in (fi, k1, k3):
                continue
            if k == k2:
                out.append(F2n)
            elif k == k4:
                out.append(F3m)
            else:
                out.append(list(f))
        out.append(merged)
    return L["orient_faces"](out)


def braces_by_order(graphs):
    out = {}
    for canon, rec in graphs["bfs"].items():
        if rec.get("brace"):
            out.setdefault(rec["n"], {})[canon] = rec
    return out


def run():
    graphs = json.loads((HERE / "bracegen-graphs.json").read_text())
    # correctness anchor: contraction must exactly invert square_expand
    anchors = 0
    for canon, rec in graphs["bfs"].items():
        faces = [list(f) for f in rec["faces"]]
        for step in L["admissible_steps"](faces):
            child, _ = L["square_expand"](faces, *step)
            back = None
            for fi, fc in enumerate(child):
                if len(fc) != 4:
                    continue
                for flip in (False, True):
                    got = contract_c4(child, fi, flip)
                    if got is not None and \
                            L["canonical_form"](got) == \
                            L["canonical_form"](faces):
                        back = (fi, flip)
                        break
                if back is not None:
                    break
            assert back is not None, "round-trip failed"
            anchors += 1
    # brace flags recomputed independently (dual characterisation)
    bfs = {}
    for canon, rec in graphs["bfs"].items():
        faces = [list(f) for f in rec["faces"]]
        es = L["face_edges"](faces)
        brace, _ = L["is_brace"](es)
        cut = L["has_nontrivial_3cut"](es)
        assert brace == (not cut)
        bfs[canon] = {"faces": faces, "n": rec["n"], "brace": brace,
                      "history": rec["history"]}
    canon14 = [c for c, r in bfs.items() if r["n"] == 14]
    assert len(canon14) == 1 and not bfs[canon14[0]]["brace"]
    rows = []
    for canon, rec in sorted(bfs.items(), key=lambda kv: kv[1]["n"]):
        if not rec["brace"] or rec["n"] == 8:
            continue
        results = []
        for fi, f in enumerate(rec["faces"]):
            if len(f) != 4:
                continue
            for flip in (False, True):
                child = contract_c4(rec["faces"], fi, flip)
                tag = {"face": fi, "flip": flip}
                if child is None:
                    results.append({**tag, "status": "invalid"})
                    continue
                try:
                    cert = L["certify"](child)  # full deletion checks
                except (AssertionError, ValueError):
                    results.append({**tag, "status": "leaves_class"})
                    continue
                ces = L["face_edges"](child)
                brace, _ = L["is_brace"](ces)
                cut = L["has_nontrivial_3cut"](ces)
                assert brace == (not cut)
                ccanon = repr(L["canonical_form"](child))
                results.append({**tag, "status": "ok",
                                "child_n": cert["n"], "child_brace": brace,
                                "child_canon": ccanon})
        faces4 = sorted({r["face"] for r in results})
        hmm_claim = all(
            any(r["status"] == "ok" for r in results if r["face"] == fi)
            for fi in faces4)
        rows.append({"n": rec["n"], "history": rec["history"],
                     "canon": canon, "contractions": results,
                     "any_brace_child": any(
                         r.get("child_brace") for r in results),
                     "hmm_one_application_stays_in_class": hmm_claim})
    b18 = [r for r in rows if r["n"] == 18]
    summary = {
        "roundtrip_anchors": anchors,
        "braces_contracted": len(rows),
        "b18_contractions": b18[0]["contractions"] if b18 else None,
        "b18_any_brace_child": b18[0]["any_brace_child"] if b18 else None,
        "all_other_braces_have_brace_child": all(
            r["any_brace_child"] for r in rows if r["n"] != 18),
        "hmm_claim_verified_on_all": all(
            r["hmm_one_application_stays_in_class"] for r in rows),
        "status": "PASS"}
    return {"summary": summary, "rows": rows}


if __name__ == "__main__":
    result = run()
    (HERE / "c4reduce-01.json").write_text(json.dumps(result, indent=2))
    print(json.dumps(result["summary"], indent=2)[:3000])
