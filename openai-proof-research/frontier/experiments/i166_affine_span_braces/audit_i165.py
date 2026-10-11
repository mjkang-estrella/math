"""I166 independent audit of I165's encoded mathematical interfaces.

Reads I165's recorded payload JSONs as DATA ONLY (no I165 code executes).
Every check uses lib166, written independently for I166.  Output: audit-01.json.

Audited interfaces:
  A. Class certificates of the decisive 50/54-vertex pair (simplicity,
     cubicity, bipartition, 3-vertex-connectivity, Euler characteristic,
     rotation systems) rebuilt from the recorded oriented face lists.
  B. The recorded old/new Hamiltonian-cycle sets: validity, cardinalities
     576/572, and set-equality with two independent re-enumerations.
  C. The boundary decomposition N00/Pux/Pvy/D11 = 138/52/38/44 recomputed
     from the recorded step, plus the complete six-fibre identity on
     independently enumerated cycle sets (I165's Proposition E instance).
  D. Admissibility of the recorded step: common face, four distinct
     terminals, odd residual paths of lengths 3 and 11.
  E. Base certificates A (32 vertices) and A' (36): counts 102/124,
     omitted-port profiles (34,62,6)/(36,54,34), affine ranks 17/19.
  F. Prism attachment profile (2, m-2, 2) at m=10 and affine rank 11.
  G. Infinite-family arithmetic from the base profiles: h = 62m-44,
     h' = 54m+32, n = 2m+30, gain = 76-8m; plus direct finite checks at
     m = 4, 6, 8, 10, 12 by independent construction and enumeration, and
     splice/expansion commutation at all five tested orders (a
     dart-rooted rotation-system canonical form, itself anchored against
     the published census OEIS A007083).
  H. Affine ranks 26/28 of the decisive pair (independent elimination).
  I. Facial-toggle failure witness on L8 step (1,3,7): unique lost cycle,
     both arc toggles split into two components with degree profile
     [1,1,2,...], exactly as recorded.
  J. Short-side injection Pux = N00 on short-side steps of L8/L10 and of
     two independently grown expansion graphs (delete/add bijection).
"""
import json
import runpy
from pathlib import Path

HERE = Path(__file__).resolve().parent
I165 = HERE.parent / "i165_square_expansion_multiplicity"
L = runpy.run_path(str(HERE / "lib166.py"))


def load(name):
    return json.loads((I165 / name).read_text())


def both(es, cap=None):
    a, done = L["hamilton_cycles_dfs"](es, visit_cap=cap)
    if not done:
        return a, False
    b = L["hamilton_cycles_matching"](es)
    assert a == b, "independent enumerators disagree"
    return a, True


def ports(hs, v, neighbors):
    return [sum(1 for h in hs if L["ue"](v, w) not in h) for w in neighbors]


def spanning_paths(edges, a, b):
    """All vertex-spanning a-b paths as edge frozensets (plain DFS)."""
    nb = L["neighbor_map"](edges)
    out = set()

    def rec(path, used, acc):
        t = path[-1]
        if t == b:
            if len(path) == len(nb):
                out.add(frozenset(acc))
            return
        for w in nb[t]:
            if w not in used:
                rec(path + [w], used | {w}, acc + [L["ue"](t, w)])

    rec([a], {a}, [])
    return out


def d11_family(edges, e, f, u, corner):
    """2-factor PM complements with e,f present and u,corner separated."""
    nb = L["neighbor_map"](edges)
    verts = sorted(nb)
    out = set()
    for mm in L["perfect_matchings"](edges):
        comp = frozenset(edges) - mm
        if e not in comp or f not in comp:
            continue
        comps = L["components_of"](verts, sorted(comp))
        if len(comps) == 2:
            cu = next(c for c in comps if u in c)
            if corner not in cu:
                out.add(comp)
    return out


def affine_rank_of(edges, hs):
    return L["rank_rows"](L["cycle_differences"](edges, hs))


def run():
    report = {}
    decisive = load("decisive-03.json")
    cert_old = decisive["certificate"]
    cert_new = decisive["expanded_certificate"]

    # ---- A: certificates rebuilt from recorded faces
    faces_old = [list(f) for f in cert_old["faces"]]
    faces_new = [list(f) for f in cert_new["faces"]]
    my_old = L["certify"](faces_old)
    my_new = L["certify"](faces_new)
    assert my_old["n"] == 50 and my_new["n"] == 54
    assert my_old["bipartition_sizes"] == [25, 25]
    assert my_new["bipartition_sizes"] == [27, 27]
    assert L["face_edges"](faces_old) == [tuple(e) for e in cert_old["edges"]]
    assert L["face_edges"](faces_new) == [tuple(e) for e in cert_new["edges"]]
    # recorded rotation systems agree with mine
    for cert, mine in ((cert_old, my_old), (cert_new, my_new)):
        for v, rot in cert["rotation"].items():
            assert tuple(rot) == tuple(mine["rotation"][int(v)])
    # recorded bipartitions agree with mine
    for cert, mine in ((cert_old, my_old), (cert_new, my_new)):
        recorded = [set(p) for p in cert["bipartition"]]
        mine_parts = [set(v for v, c in mine["color"].items() if c == k)
                      for k in (0, 1)]
        assert recorded == mine_parts or recorded == mine_parts[::-1]
    report["A_certificates"] = {"n_old": 50, "n_new": 54,
                                "deletion_pairs_old": my_old["deletion_pairs_checked"],
                                "deletion_pairs_new": my_new["deletion_pairs_checked"],
                                "status": "PASS"}

    # ---- B: recorded cycles valid and independently reproducible
    es_old = L["face_edges"](faces_old)
    es_new = L["face_edges"](faces_new)
    rec_old = {frozenset(map(tuple, h)) for h in decisive["old_cycles"]}
    rec_new = {frozenset(map(tuple, h)) for h in decisive["new_cycles"]}
    assert len(rec_old) == 576 and len(rec_new) == 572
    nb_old = L["neighbor_map"](es_old)
    nb_new = L["neighbor_map"](es_new)
    for rec, es, nb, n in ((rec_old, es_old, nb_old, 50),
                           (rec_new, es_new, nb_new, 54)):
        for h in rec:
            assert len(h) == n and all(e in es for e in h)
            assert len(L["components_of"](sorted(nb), sorted(h))) == 1
            deg = L["neighbor_map"](sorted(h))
            assert all(len(deg[v]) == 2 for v in nb)
    my_old_cycles, done1 = both(es_old)
    assert done1
    my_new_cycles, done2 = both(es_new)
    assert done2
    assert my_old_cycles == rec_old and my_new_cycles == rec_new
    report["B_cycle_sets"] = {"h": 576, "h_prime": 572,
                              "two_enumerators_agree": True,
                              "sets_equal_recorded": True, "status": "PASS"}

    # ---- C + D: step admissibility and boundary decomposition
    fi, i, j = decisive["step"]
    face = faces_old[fi]
    recorded_face = [9, 25, 24, 8, 20, 29, 28, 41, 40, 39, 38, 37, 36, 35, 34, 33]
    assert list(face) == recorded_face
    u, v = face[i], face[i + 1]
    y, x = face[j], face[(j + 1) % len(face)]   # I165 tuple order (u,v,x,y)
    assert (u, v, x, y) == tuple(decisive["terminals"]) == (25, 24, 28, 29)
    assert len({u, v, x, y}) == 4
    assert (j - i) % 2 == 0 and (len(face) - (j - i)) % 2 == 0
    assert (j - i - 1, len(face) - (j - i) - 1) == (3, 11)  # odd residuals
    e, f = L["ue"](u, v), L["ue"](x, y)
    k_edges = [z for z in es_old if z not in (e, f)]
    n00 = {h for h in my_old_cycles if e not in h and f not in h}
    pux, pdone1 = L["spanning_paths_pruned"](k_edges, u, x)
    pvy, pdone2 = L["spanning_paths_pruned"](k_edges, v, y)
    assert pdone1 and pdone2
    d11 = d11_family(es_old, e, f, u, x)
    assert (len(n00), len(pux), len(pvy), len(d11)) == (138, 52, 38, 44)
    assert 576 - 138 + 52 + 38 + 44 == 572
    report["D_admissibility"] = {"face": recorded_face, "residuals": [3, 11],
                                 "distinct_terminals": True, "status": "PASS"}
    # six-fibre identity: restrict my new cycles through the recorded arms
    # new vertices are the four labels absent from the old graph
    new_vs = sorted(set(L["neighbor_map"](es_new)) - set(nb_old))
    assert len(new_vs) == 4
    # identify arms: the four edges joining old terminals to new vertices
    arms = {}
    for t in (u, v, x, y):
        for w in nb_new[t]:
            if w in new_vs:
                arms[L["ue"](t, w)] = t
    assert len(arms) == 4
    exp = {"N10": {h for h in my_old_cycles if e in h and f not in h},
           "N01": {h for h in my_old_cycles if f in h and e not in h},
           "N11": {h for h in my_old_cycles if e in h and f in h},
           "N00": n00, "Pux": pux, "Pvy": pvy, "D11": d11}
    actual = {k: [] for k in ("N10", "N01", "N11", "Pux", "Pvy", "D11")}
    k_set = set(k_edges)
    for h in my_new_cycles:
        used = frozenset(arms[w] for w in h if w in arms)
        exterior = h & k_set
        if len(used) == 2:
            table = {frozenset((u, v)): ("N10", exterior | {e}),
                     frozenset((x, y)): ("N01", exterior | {f}),
                     frozenset((u, x)): ("Pux", exterior),
                     frozenset((v, y)): ("Pvy", exterior)}
            name, witness = table[used]
        else:
            assert len(used) == 4
            witness = exterior | {e, f}
            name = ("N11" if len(L["components_of"](sorted(nb_old),
                                                    sorted(witness))) == 1
                    else "D11")
        actual[name].append(frozenset(witness))
    fibres = {}
    for name in actual:
        assert len(actual[name]) == len(set(actual[name])), name
        assert set(actual[name]) == exp[name], name
        fibres[name] = len(actual[name])
    assert fibres == {"N10": 200, "N01": 92, "N11": 146,
                      "Pux": 52, "Pvy": 38, "D11": 44}
    assert fibres == {k: v for k, v in decisive["arm_fibres"].items()}
    report["C_boundary"] = {"N00": 138, "Pux": 52, "Pvy": 38, "D11": 44,
                            "six_fibres_exact": True, "status": "PASS"}

    # ---- E: base pieces
    base_faces = [list(fc) for fc in decisive["base_certificate"]["faces"]]
    base_new_faces = [list(fc)
                      for fc in decisive["base_expanded_certificate"]["faces"]]
    cb = L["certify"](base_faces)
    cbn = L["certify"](base_new_faces)
    assert cb["n"] == 32 and cbn["n"] == 36
    es_b = L["face_edges"](base_faces)
    es_bn = L["face_edges"](base_new_faces)
    hb, d1 = both(es_b)
    hbn, d2 = both(es_bn)
    assert d1 and d2
    assert len(hb) == 102 and len(hbn) == 124
    pa = ports(hb, 21, [9, 22, 28])
    pb = ports(hbn, 21, [9, 22, 28])
    assert pa == [34, 62, 6] and pb == [36, 54, 34]
    ra = affine_rank_of(es_b, hb)
    rb = affine_rank_of(es_bn, hbn)
    assert ra == 17 == 32 // 2 + 1 and rb == 19 == 36 // 2 + 1
    report["E_base_pieces"] = {"A": {"n": 32, "h": 102, "d": ra,
                                     "ports": pa},
                               "A_prime": {"n": 36, "h": 124, "d": rb,
                                           "ports": pb},
                               "status": "PASS"}

    # ---- F: prism attachment profile
    prism_faces = L["prism_faces"](10)
    es_p = L["face_edges"](prism_faces)
    hp, dp = both(es_p)
    assert dp and len(hp) == 12
    assert ports(hp, 0, [1, 10, 9]) == [2, 8, 2]
    rp = affine_rank_of(es_p, hp)
    assert rp == 11 == 20 // 2 + 1
    report["F_prism_L10"] = {"h": 12, "d": rp, "ports": [2, 8, 2],
                             "status": "PASS"}

    # ---- G: family arithmetic and direct finite checks
    amp = load("amplification-01.json")
    profs = {k: v["ports"] for k, v in amp["profiles"].items()}
    assert profs["N00"] == [5, 16, 0] and profs["Pux"] == [3, 4, 0]
    assert profs["Pvy"] == [1, 1, 21] and profs["D11"] == [3, 3, 7]
    assert profs["h"] == [34, 62, 6] and profs["h_prime"] == [36, 54, 34]

    def formula(p):
        return lambda m: 2 * p[0] + (m - 2) * p[1] + 2 * p[2]

    fh, fh2 = formula(profs["h"]), formula(profs["h_prime"])
    for m in range(4, 26, 2):
        assert fh(m) == 62 * m - 44 and fh2(m) == 54 * m + 32
        assert (fh2(m) - fh(m)) == 76 - 8 * m
        assert 32 + 2 * m - 2 == 2 * m + 30
    # profile sums are consistent: N00+Pux+Pvy+D11 over h'-h identity
    for m in (4, 10, 24):
        lhs = (62 * m - 44) - (2 * 5 + (m - 2) * 16 + 2 * 0) \
            + (2 * 3 + (m - 2) * 4) + (2 * 1 + (m - 2) * 1 + 2 * 21) \
            + (2 * 3 + (m - 2) * 3 + 2 * 7)
        assert lhs == 54 * m + 32
    direct = []
    for m in (4, 6, 8, 10, 12):
        gm, _ = L["splice_faces"](base_faces, 21, L["prism_faces"](m), 0,
                                  {9: 1, 22: m, 28: m - 1})
        cg = L["certify"](gm)
        assert cg["n"] == 2 * m + 30
        hg, dg = both(L["face_edges"](gm))
        assert dg
        assert len(hg) == 62 * m - 44, (m, len(hg))
        g2, _ = L["splice_faces"](base_new_faces, 21, L["prism_faces"](m), 0,
                                  {9: 1, 22: m, 28: m - 1})
        cg2 = L["certify"](g2)
        assert cg2["n"] == 2 * m + 34
        hg2, dg2 = both(L["face_edges"](g2))
        assert dg2
        assert len(hg2) == 54 * m + 32, (m, len(hg2))
        direct.append({"m": m, "n": 2 * m + 30, "h": len(hg),
                       "h_prime": len(hg2), "gain": len(hg2) - len(hg)})
        # splice/expansion commutation at every tested m: expand G_m at
        # the corresponding step and compare canonical forms with G'_m
        if True:
            found = None
            for step in L["admissible_steps"](gm):
                f2, (uu, vv, xx, yy) = L["square_expand"](gm, *step)
                if {L["ue"](uu, vv), L["ue"](xx, yy)} == \
                        {L["ue"](24, 25), L["ue"](28, 29)}:
                    assert found is None
                    found = f2
            assert found is not None
            assert L["canonical_form"](found) == L["canonical_form"](g2)
    report["G_family"] = {"formula_h": "62m-44", "formula_h_prime": "54m+32",
                          "order": "2m+30", "gain": "76-8m",
                          "direct_checks": direct,
                          "commutation_checked_m": [4, 6, 8, 10, 12],
                          "status": "PASS"}

    # ---- H: affine ranks of the decisive pair
    r_old = affine_rank_of(es_old, my_old_cycles)
    r_new = affine_rank_of(es_new, my_new_cycles)
    assert r_old == 26 == 50 // 2 + 1 and r_new == 28 == 54 // 2 + 1
    report["H_affine"] = {"d_old": r_old, "d_new": r_new,
                          "both_full": True, "status": "PASS"}

    # ---- I: facial-toggle failure witness
    fb = load("fallback-02.json")
    wit = fb["facial_toggle_failure"]
    assert wit["prism_m"] == 8 and wit["step"] == [1, 3, 7]
    faces8 = L["prism_faces"](8)
    rec_face = faces8[1]
    _, (u8, v8, x8, y8) = L["square_expand"](faces8, 1, 3, 7)
    es8 = L["face_edges"](faces8)
    hs8, d8 = both(es8)
    assert d8 and len(hs8) == 10
    e8, f8 = L["ue"](u8, v8), L["ue"](x8, y8)
    lost = {h for h in hs8 if e8 not in h and f8 not in h}
    assert len(lost) == 1
    h0 = next(iter(lost))
    recorded_cycle = frozenset(map(tuple, wit["cycle"]))
    assert recorded_cycle == h0
    toggles = []
    for arc_info in wit["toggles"]:
        arc = arc_info["arc"]
        arc_edges = {L["ue"](a, b) for a, b in zip(arc, arc[1:])}
        toggled = h0 ^ arc_edges
        assert frozenset(map(tuple, arc_info["output_edges"])) == toggled
        comps = L["components_of"](list(range(16)), sorted(toggled))
        assert len(comps) == 2
        assert [sorted(c) for c in comps] == arc_info["components"]
        from collections import Counter as _C
        assert _C(len(L["neighbor_map"](sorted(toggled)).get(v, []))
                  for v in range(16)) == _C({2: 14, 1: 2})
        toggles.append({"arc": arc, "components": [sorted(c) for c in comps]})
    report["I_facial_toggle"] = {"lost_cycles": 1, "toggles": toggles,
                                 "both_split": True, "status": "PASS"}

    # ---- J: short-side injection P-family = N00 on short-side steps
    checks = 0

    def short_side_check(faces, step):
        fi, i, j = step
        f0 = faces[fi]
        if (j - i) != 2 and (len(f0) - (j - i)) != 2:
            return False
        _, (uu, vv, xx, yy) = L["square_expand"](faces, *step)
        e0, f0e = L["ue"](uu, vv), L["ue"](xx, yy)
        es0 = L["face_edges"](faces)
        hs0, dd = L["hamilton_cycles_dfs"](es0)
        assert dd
        n00_0 = {h for h in hs0 if e0 not in h and f0e not in h}
        k0 = [z for z in es0 if z not in (e0, f0e)]
        # with (u,v,x,y) = (f[i],f[i+1],f[j],f[j+1]), the path classes pair
        # (v,x) and (u,y); the short residual side is one of these edges
        if (j - i) == 2:
            a, b = vv, xx      # residual arc v - ... - x is a single edge
        else:
            a, b = uu, yy      # residual arc y - ... - u is a single edge
        assert L["ue"](a, b) in k0, "short residual edge missing"
        paths = spanning_paths(k0, a, b)
        assert paths == {h - {L["ue"](a, b)} for h in n00_0}
        # cross-validate the pruned enumerator against the plain one here
        pruned, done = L["spanning_paths_pruned"](k0, a, b)
        assert done and pruned == paths
        return True

    for m in (8, 10):
        fm = L["prism_faces"](m)
        for step in L["admissible_steps"](fm):
            if short_side_check(fm, step):
                checks += 1
    # two independently grown graphs, all their short-side steps
    g1 = L["prism_faces"](6)
    g1, _ = L["square_expand"](g1, 0, 0, 4)
    g2 = L["cube_faces"]()
    g2 = L["cube_expand_vertex"](g2, 3)
    for gg in (g1, g2):
        L["certify"](gg)
        for step in L["admissible_steps"](gg):
            if short_side_check(gg, step):
                checks += 1
    assert checks >= 20
    report["J_short_side"] = {"bijection_checks": checks, "status": "PASS"}

    report["verdict"] = "ALL AUDITED I165 INTERFACES PASS INDEPENDENTLY"
    return report


if __name__ == "__main__":
    report = run()
    (HERE / "audit-01.json").write_text(json.dumps(report, indent=2))
    print(json.dumps(report, indent=2))
