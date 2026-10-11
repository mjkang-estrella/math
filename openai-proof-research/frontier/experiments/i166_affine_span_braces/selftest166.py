"""Toolkit self-anchoring: every fact asserted here is classical and tiny.

Anchors used (all directly verifiable by hand):
  * cube Q3: 8 vertices, 6 Hamiltonian cycles, affine dimension 5 = 8/2+1.
  * even prism L_m: m+2 Hamiltonian cycles (rungs-omission argument),
    affine dimension m+1 = n/2+1 for m = 4,6,8,10.
  * the two independent enumerators agree on every anchor graph.
  * every even prism is a brace (2-extendable); the cube is a brace.
  * square expansion identity h' = h - N00 + Pux + Pvy + D11 on samples.
"""
import runpy
from pathlib import Path

L = runpy.run_path(str(Path(__file__).with_name("lib166.py")))


def both_enumerators(es, cap=None):
    a, done = L["hamilton_cycles_dfs"](es, visit_cap=cap)
    assert done, "selftest graphs must exhaust"
    b = L["hamilton_cycles_matching"](es)
    assert a == b, "enumerator disagreement"
    return a


def run():
    out = {"prisms": [], "cube": {}, "expansion_identity_checks": 0}
    for m in (4, 6, 8, 10):
        faces = L["prism_faces"](m)
        cert = L["certify"](faces)
        assert cert["n"] == 2 * m
        es = L["face_edges"](faces)
        hs = both_enumerators(es)
        assert len(hs) == m + 2, (m, len(hs))
        rank = L["rank_rows"](L["cycle_differences"](es, hs))
        assert rank == m + 1, (m, rank)
        brace, _ = L["is_brace"](es)
        assert brace
        assert not L["has_nontrivial_3cut"](es)
        out["prisms"].append({"m": m, "n": 2 * m, "h": len(hs), "d": rank})
    cube = L["cube_faces"]()
    es = L["face_edges"](cube)
    hs = both_enumerators(es)
    assert len(hs) == 6
    assert L["rank_rows"](L["cycle_differences"](es, hs)) == 5
    brace, _ = L["is_brace"](es)
    assert brace and not L["has_nontrivial_3cut"](es)
    out["cube"] = {"n": 8, "h": 6, "d": 5}
    # expansion identity on every admissible step of L_8 and a sample on L_12
    for m in (8, 12):
        faces = L["prism_faces"](m)
        es = L["face_edges"](faces)
        hs = both_enumerators(es)
        steps = list(L["admissible_steps"](faces))
        if m == 12:
            steps = steps[::7]
        for step in steps:
            new, (u, v, x, y) = L["square_expand"](faces, *step)
            cert = L["certify"](new)
            assert cert["n"] == 2 * m + 4
            e, f = L["ue"](u, v), L["ue"](x, y)
            # arm pairs across the square: (u, f[j+1]) and (v, f[j])
            fj1 = faces[step[0]][(step[2] + 1) % len(faces[step[0]])]
            fj = faces[step[0]][step[2]]
            n00 = sum(1 for h in hs if e not in h and f not in h)
            k_edges = [z for z in es if z not in (e, f)]
            nhs = both_enumerators(L["face_edges"](new))
            pux = L["hamilton_cycles_dfs"](k_edges, visit_cap=None)
            # count spanning u-x / v-y paths in K = G - e - f via DFS on
            # paths: reuse the cycle enumerator on K plus a closing gadget is
            # overkill; direct count below.
            def count_paths(a, b):
                nb = L["neighbor_map"](k_edges)
                total = [0]
                def rec(path, used):
                    t = path[-1]
                    if t == b:
                        if len(path) == len(nb):
                            total[0] += 1
                        return
                    for w in nb[t]:
                        if w not in used:
                            rec(path + [w], used | {w})
                rec([a], {a})
                return total[0]
            p_ux, p_vy = count_paths(u, fj1), count_paths(v, fj)
            # D11: 2-factors complementing a matching, e,f on different comps
            d11 = 0
            for mm in L["perfect_matchings"](es):
                comp = set(es) - set(mm)
                comps = L["components_of"](sorted(L["neighbor_map"](es)),
                                           sorted(comp))
                if len(comps) == 2 and e in comp and f in comp:
                    cu = next(c for c in comps if u in c)
                    if fj1 not in cu:
                        d11 += 1
            assert len(nhs) == len(hs) - n00 + p_ux + p_vy + d11
            out["expansion_identity_checks"] += 1
    # splice sanity: cube splice cube has 14 vertices; enumerators agree
    c1, c2 = L["cube_faces"](), L["cube_faces"]()
    nb2 = L["neighbor_map"](L["face_edges"](c2))
    spliced, _ = L["splice_faces"](c1, 0, c2, 0, {1: 1, 2: 2, 4: 4})
    cert = L["certify"](spliced)
    assert cert["n"] == 14
    both_enumerators(L["face_edges"](spliced))
    out["splice_sanity_n"] = cert["n"]
    # canonical-form anchors (dart-rooted rotation-system code)
    g0 = L["cube_expand_vertex"](cube, 0)
    c0 = L["canonical_form"](g0)
    assert c0 == L["canonical_form"](L["cube_expand_vertex"](cube, 3))
    assert c0 == L["canonical_form"](L["cube_expand_vertex"](cube, 7))
    import random
    nb = L["neighbor_map"](L["face_edges"](g0))
    perm = sorted(nb)
    random.Random(166).shuffle(perm)
    mp = dict(zip(sorted(nb), perm))
    relabelled = L["orient_faces"]([[mp[v] for v in f] for f in g0])
    assert L["canonical_form"](relabelled) == c0
    p6 = L["prism_faces"](6)
    assert L["canonical_form"](p6) == L["canonical_form"](
        L["square_expand"](cube, 0, 0, 2)[0])
    e1 = L["square_expand"](cube, 0, 0, 2)[0]
    e2 = L["square_expand"](e1, 0, 0, 2)[0]
    e3 = L["square_expand"](e1, 0, 1, 3)[0]
    assert L["canonical_form"](e2) != L["canonical_form"](e3)
    out["canonical_anchors"] = 5
    return out


if __name__ == "__main__":
    import json
    print(json.dumps(run(), indent=2))
