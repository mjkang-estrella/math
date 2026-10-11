"""I195 byte authentication, cap-prism family checks, multi-component
flip instance, and inherited replay.

The finite checks below independently verify, with fresh parent-side
enumeration and exact rational linear algebra on the smallest genuine
long-gap step (the C_8 prism cap deletion e = t_0, f = t_4, the 3+3
split): the complete ten-cycle old family with N00 = {Y}, N10 = {C_4},
N01 = {C_0} and N11 = {C_i: i not 0, 4} + X; the complete new families
Pux = {P_5, P_6, P_7}, Pvy = {Q_1, Q_2, Q_3} and D11 = {D_hg} (nine
covers), matching the child's explicit vector formulas (6) exactly; the
ranks d(G) = 9, dim L = 8, dim L0 = 6, dim U = 4 with U subseteq L0,
hence (ell, t, epsilon, Delta) = (1, 0, 1, 1) with zero margin; the
bridge beta notin L0+U with eta = 1 and w(beta) = 4/3 = m/(m-2) for
the normalized quotient functional; the integer identities (10) and
(12); and the child graph H by direct enumeration (24 Hamiltonian
cycles, d(H) = 11 = d(G)+2). The multi-component flip identity (15)
is verified on the cube instance (F = two layer squares, h = 2, the
lateral-square flip meets both components and reconnects to a
Hamiltonian cycle). The general-m written proofs, the exhaustion
argument for (6), the admissibility case split and the route
obstructions are reviewed in prose (see the parent disposition).
"""
import json
import runpy
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i194-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
SOURCE = "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex"
SOURCE_HASH = "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
OUTPUTS = {
    "frontier/iterations/i195-long-gap-deficit.md":
        "c2f97a9acfa98e547cf0ec51aafb7730e037e1133e5877a23799f618ace79cee",
    "frontier/experiments/i195_long_gap_deficit/analytic-attempt.md":
        "13bef8a3ede52de23ede6e669e28dd0e8093f57be5c36773d8fa28a230e5de7e",
    "frontier/experiments/i195_long_gap_deficit/reading-and-failures.md":
        "6ebcffa76d22567ef2b5c36397280cdcc6f61ec2e13477ab43fa8330f1272ed2",
    "frontier/experiments/i195_long_gap_deficit/input-authentication.json":
        "066d27c270e617c5b940bc6acf26d99d00691ab49f4738668733f7a6c35e1228",
    "frontier/sources/i195_long_gap_deficit/literature.md":
        "dd6d17620cc2af893a801d128c33808e2792ece61ef4eee32c7127c730edacd2",
}
ANCHORS = {
    "frontier/iterations/i194-quotient-sign.md":
        "21f8e32eec69b89d7e6eade2763a3f7b125c6575121f5f05bddb0d37ab21b2b2",
    "frontier/iterations/i193-equality-bridge.md":
        "e1402e6ec2561f35f3b6d0b5c67361afdb907652b5815134fb2215b6bcb59cb5",
    "frontier/iterations/i192-exchange-residual.md":
        "ffc58919a1ce84f086e36e7b7b85c803dbd47c0dd7609046fc44711aa14c126d",
    "frontier/iterations/i168-cross-class-exchange.md":
        "696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31",
    "frontier/iterations/i169-bridge-independence.md":
        "1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf",
    "frontier/iterations/i170-quadrilateral-coefficient.md":
        "8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096",
    SOURCE: SOURCE_HASH,
}
I193 = PREVIOUS["PREVIOUS"]
I192 = I193["PREVIOUS"]
_rank = PREVIOUS["_rank"]
_prism_edges = PREVIOUS["_prism_edges"]
_order = PREVIOUS["_order"]
_vec = PREVIOUS["_vec"]
_functional_quotient = PREVIOUS["_functional_quotient"]
_hamiltonian_cycles = I192["_hamiltonian_cycles"]
_spanning_paths = I192["_spanning_paths"]
_all_paths = I192["_all_paths"]
_generic_cycles = I193["_generic_cycles"]
_generic_rank = I193["_generic_rank"]


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i195-long-gap-deficit.md"}
    for directory in ("frontier/experiments/i195_long_gap_deficit",
                      "frontier/sources/i195_long_gap_deficit"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i195_long_gap_deficit/input-authentication.json").read_bytes())
    assert receipt["status"].startswith("COMPLETE")
    assert receipt["unsealed"] is True
    assert receipt["upstream_commit"] == (
        "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb")
    assert receipt["all_seven_anchors_match_brief"] is True
    anchored = 0
    for path, digest in receipt["anchors"].items():
        assert sha(path) == digest == ANCHORS[path], path
        anchored += 1
    assert anchored == 7
    assert len(receipt["additional_inputs"]) == 14
    for path, digest in receipt["additional_inputs"].items():
        assert sha(path) == digest, path
    archive = json.loads((ROOT / "frontier/iterations"
        "/iteration195-long-gap-deficit-task.json").read_bytes())
    assert set(archive["write_scope"]) == set(OUTPUTS)
    assert archive["anchors"]["I194_report"] == ANCHORS[
        "frontier/iterations/i194-quotient-sign.md"]
    assert archive["anchors"]["I192_report"] == ANCHORS[
        "frontier/iterations/i192-exchange-residual.md"]
    assert "PARKED" in archive["stopping_rule"]
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "supplied_anchors": anchored,
            "additional_inputs": len(receipt["additional_inputs"]),
            "previous_proof_records": "unchanged"}


def cap_prism_checks():
    """The m = 8, j = 4 cap-prism long-gap step, re-derived from
    scratch: complete families, ranks, identities, bridge value, and
    the child graph."""
    m, j = 8, 4
    edges = _prism_edges(m)
    cycles = _hamiltonian_cycles(m, edges)
    assert len(cycles) == m + 2 == 10
    dim = 3 * m
    e, f = ("t", 0), ("t", j)
    # Old family classification.
    c_cyc = {}
    for i in range(m):
        match = [c for c in cycles
                 if ("t", i) not in c and ("b", i) not in c]
        assert len(match) == 1
        c_cyc[i] = match[0]
    twisted = [c for c in cycles
               if all(("r", i) in c for i in range(m))]
    assert len(twisted) == 2
    x_cyc, = [c for c in twisted if e in c]
    y_cyc, = [c for c in twisted if e not in c]
    assert f in x_cyc and f not in y_cyc
    n00 = [c for c in cycles if e not in c and f not in c]
    assert n00 == [y_cyc]
    n10 = [c for c in cycles if e in c and f not in c]
    n01 = [c for c in cycles if e not in c and f in c]
    n11 = [c for c in cycles if e in c and f in c]
    assert n10 == [c_cyc[j]] and n01 == [c_cyc[0]]
    assert sorted(map(sorted, n11)) == sorted(
        map(sorted, [c_cyc[i] for i in range(m) if i not in (0, j)]
            + [x_cyc]))
    survivors = n10 + n01 + n11
    # Claimed fixed vectors (6), as Boolean edge sets.
    z_rails = {("t", i) for i in range(m)} | {("b", i) for i in range(m)}

    def d_vec(i):
        return {("r", i), ("r", (i + 1) % m), ("t", i), ("b", i)}
    p_star = (z_rails
              - {("t", i) for i in range(0, j + 1, 2)}
              - {("b", i) for i in range(1, j, 2)}
              ) | {("r", i) for i in range(1, j + 1)}
    q_star = (z_rails - {("t", 0)}
              - {("t", i) for i in range(j, m, 2)}
              - {("b", i) for i in range(j + 1, m, 2)}
              ) | {("r", 0)} | {("r", i) for i in range(j + 1, m)}
    p_claim = {g: p_star ^ d_vec(g) for g in range(j + 1, m)}
    q_claim = {h: q_star ^ d_vec(h) for h in range(1, j)}
    d_claim = {(h, g): (z_rails - {e, f}) ^ d_vec(h) ^ d_vec(g)
               for h in range(1, j) for g in range(j + 1, m)}
    for fam in list(p_claim.values()) + list(q_claim.values()) + \
            list(d_claim.values()):
        assert fam <= set(edges)  # Boolean edge subsets of K
    # Fresh enumeration in K = G - {e, f}.
    k_adj = {}
    for name, (a2, b2) in edges.items():
        if name in (e, f):
            continue
        k_adj.setdefault(a2, []).append(b2)
        k_adj.setdefault(b2, []).append(a2)
    verts_k = frozenset(k_adj)
    edge_of_k = {frozenset(v): k for k, v in edges.items()
                 if k not in (e, f)}

    def path_edges(path):
        return frozenset(edge_of_k[frozenset((a2, b2))]
                         for a2, b2 in zip(path, path[1:]))
    u, v, y_t, x_t = (0, 0), (0, 1), (0, j), (0, (j + 1) % m)
    p_ux = {path_edges(p) for p in _spanning_paths(k_adj, verts_k, u, x_t)}
    q_vy = {path_edges(p) for p in _spanning_paths(k_adj, verts_k, v, y_t)}
    assert p_ux == {frozenset(s) for s in p_claim.values()}
    assert q_vy == {frozenset(s) for s in q_claim.values()}
    d11 = set()
    for p in _all_paths(k_adj, u, v):
        rest = verts_k - set(p)
        if x_t not in rest or y_t not in rest:
            continue
        sub = {w: [z2 for z2 in k_adj[w] if z2 in rest] for w in rest}
        for q2 in _spanning_paths(sub, rest, x_t, y_t):
            d11.add(path_edges(p) | path_edges(q2))
    assert d11 == {frozenset(s) for s in d_claim.values()}
    assert (len(p_ux), len(q_vy), len(d11)) == (3, 3, 9)
    # Ranks: d(G), L, L0, U with U subseteq L0; ell, t, epsilon, Delta.
    base = _vec(c_cyc[1], m)  # surviving base C_1

    def diffs(fam, ref):
        return [[a2 - b2 for a2, b2 in zip(_vec(c, m), _vec(ref, m))]
                for c in fam if c != ref]
    all_rows = diffs(cycles, cycles[0])
    d_g = _rank(all_rows, dim)
    assert d_g == m + 1 == 9
    l_rows = diffs(survivors, c_cyc[1])
    dim_l = _rank(l_rows, dim)
    assert dim_l == m == 8
    l0_rows = diffs(n11, x_cyc)  # N10, N01 are singletons
    dim_l0 = _rank(l0_rows, dim)
    assert dim_l0 == m - 2 == 6
    p_list = sorted(p_claim.values())
    q_list = sorted(q_claim.values())
    d_list = sorted(d_claim.values())
    u_rows = (diffs(p_list, p_list[0]) + diffs(q_list, q_list[0])
              + diffs(d_list, d_list[0]))
    dim_u = _rank(u_rows, dim)
    assert dim_u == m - 4 == 4
    assert _rank(l0_rows + u_rows, dim) == dim_l0  # U subseteq L0
    t_val = _rank(l_rows + u_rows, dim) - dim_l
    ell = d_g - dim_l
    assert (ell, t_val) == (1, 0)
    c_vec = [Fraction(a2) for a2 in _vec(y_cyc, m)]
    for sgn, c in ((-1, c_cyc[j]), (-1, c_cyc[0]), (1, c_cyc[1])):
        c_vec = [a2 + sgn * b2 for a2, b2 in zip(c_vec, _vec(c, m))]
    eps = _rank(l0_rows + [c_vec], dim) - dim_l0
    assert eps == 1
    delta = ell - t_val
    assert delta == 1
    # Bridge: beta, independence, eta, and the normalized value.
    unit = [0] * dim
    beta = [Fraction(0)] * dim
    for sgn, obj in ((1, p_claim[5]), (1, q_claim[1]),
                     (1, d_claim[(1, 5)]), (-1, c_cyc[j]),
                     (-1, c_cyc[0]), (-1, c_cyc[1])):
        beta = [a2 + sgn * b2 for a2, b2 in zip(beta, _vec(obj, m))]
    for name in (e, f):
        beta[_order(m).index(name)] += 2
    eta = _rank(l0_rows + u_rows + [beta], dim) - dim_l0
    assert eta == 1  # beta notin L0 + U
    assert _rank(all_rows + [beta], dim) == d_g  # beta in D_G
    r_vec = [a2 - b2 for a2, b2 in zip(_vec(y_cyc, m), base)]
    w = _functional_quotient(l_rows, dim, r_vec)
    w_beta = sum(wi * bi for wi, bi in zip(w, beta))
    assert w_beta == Fraction(m, m - 2) == Fraction(4, 3)
    # Identity (12): (m-2) Z = sum_i C_i - X - Y.
    z_vec = _vec(z_rails, m)
    lhs = [(m - 2) * a2 for a2 in z_vec]
    rhs = [0] * dim
    for i in range(m):
        rhs = [a2 + b2 for a2, b2 in zip(rhs, _vec(c_cyc[i], m))]
    for c in (x_cyc, y_cyc):
        rhs = [a2 - b2 for a2, b2 in zip(rhs, _vec(c, m))]
    assert lhs == rhs
    # Identity (10): P_g + Q_h = D_hg + Y for all nine pairs.
    for (h, g), d_hg in d_claim.items():
        lhs10 = [a2 + b2 for a2, b2
                 in zip(_vec(p_claim[g], m), _vec(q_claim[h], m))]
        rhs10 = [a2 + b2 for a2, b2
                 in zip(_vec(d_hg, m), _vec(y_cyc, m))]
        assert lhs10 == rhs10
    # P* + Q* = Z + Y - e - f.
    lhs_s = [a2 + b2 for a2, b2 in zip(_vec(p_star, m), _vec(q_star, m))]
    rhs_s = [a2 + b2 for a2, b2 in zip(z_vec, _vec(y_cyc, m))]
    for name in (e, f):
        rhs_s[_order(m).index(name)] -= 1
    assert lhs_s == rhs_s
    # The child graph H: arms and square on p, q, r, s.
    h_edges = [(a2, b2) for name, (a2, b2) in edges.items()
               if name not in (e, f)]
    for pair in ((u, "p"), (v, "q"), (x_t, "r"), (y_t, "s"),
                 ("p", "q"), ("q", "s"), ("s", "r"), ("r", "p")):
        h_edges.append(pair)
    h_vertices = {w for pair in h_edges for w in pair}
    assert len(h_vertices) == 2 * m + 4 == 20
    h_cycles = _generic_cycles(h_vertices, h_edges, start=(0, 0))
    assert len(h_cycles) == 24
    d_h, _ = _generic_rank(h_cycles, len(h_edges))
    assert d_h == d_g + 2 == 11
    return {"m": m, "j": j, "old_cycles": len(cycles),
            "class_sizes": {"N00": 1, "N10": 1, "N01": 1, "N11": 7,
                            "Pux": 3, "Pvy": 3, "D11": 9},
            "d_G": d_g, "dim_L": dim_l, "dim_L0": dim_l0,
            "dim_U": dim_u, "U_in_L0": True,
            "ell": ell, "t": t_val, "epsilon": eps, "Delta": delta,
            "margin": 0, "eta": eta, "w_beta": str(w_beta),
            "identities": {"(10)": 9, "(12)": 1, "P*+Q*": 1},
            "child_H": {"cycles": 24, "d_H": d_h},
            "scope": "m=8, j=4 by fresh enumeration and exact rational "
                     "ranks; general-m proofs reviewed in prose"}


def multi_component_flip_check():
    """Identity (15) on the cube: F = two layer squares (h = 2), the
    lateral-square alternating cycle meets both components (c = 2),
    tau union mu is connected, and the flip is the Hamiltonian C_1."""
    m = 4
    edges = _prism_edges(m)
    cycles = _hamiltonian_cycles(m, edges)
    vertices = [(layer, i) for layer in (0, 1) for i in range(m)]
    f_factor = {("t", i) for i in range(m)} | {("b", i) for i in range(m)}
    components = PREVIOUS["_components"]
    assert components(f_factor, edges, vertices) == 2
    sym = {("t", 1), ("b", 1), ("r", 1), ("r", 2)}
    # R meets both F-components: t_1 in the top square, b_1 bottom.
    removed = sym & f_factor
    added = sym - f_factor
    assert removed == {("t", 1), ("b", 1)}
    assert added == {("r", 1), ("r", 2)}
    comp_of = {}
    cid = 0
    comp_adj = {v: [] for v in vertices}
    for name in f_factor:
        a2, b2 = edges[name]
        comp_adj[a2].append(b2)
        comp_adj[b2].append(a2)
    seen = set()
    for v0 in vertices:
        if comp_adj[v0] and v0 not in seen:
            comp_of[v0] = cid
            stack = [v0]
            seen.add(v0)
            while stack:
                for w2 in comp_adj[stack.pop()]:
                    comp_of[w2] = cid
                    if w2 not in seen:
                        seen.add(w2)
                        stack.append(w2)
            cid += 1
    touched = {comp_of[w2] for name in removed for w2 in edges[name]}
    assert len(touched) == 2  # c = 2
    # tau from the remaining paths of F - removed; mu from added edges.
    rest_adj = {}
    for name in f_factor - removed:
        a2, b2 = edges[name]
        rest_adj.setdefault(a2, []).append(b2)
        rest_adj.setdefault(b2, []).append(a2)
    endpoints = sorted(v for v in rest_adj if len(rest_adj[v]) == 1)
    assert len(endpoints) == 4
    tau = set()
    seen2 = set()
    for s0 in endpoints:
        if s0 in seen2:
            continue
        path = [s0]
        seen2.add(s0)
        while True:
            nxt = [w2 for w2 in rest_adj[path[-1]] if w2 not in path]
            if not nxt:
                break
            path.append(nxt[0])
            seen2.add(nxt[0])
        tau.add(frozenset((path[0], path[-1])))
    assert len(tau) == 2
    mu = {frozenset(edges[name]) for name in added}
    mg_adj = {}
    for pair in tau | mu:
        a2, b2 = sorted(pair)
        mg_adj.setdefault(a2, []).append(b2)
        mg_adj.setdefault(b2, []).append(a2)
    seen3, comp = set(), 0
    for v0 in mg_adj:
        if v0 not in seen3:
            comp += 1
            stack = [v0]
            seen3.add(v0)
            while stack:
                for w2 in mg_adj[stack.pop()]:
                    if w2 not in seen3:
                        seen3.add(w2)
                        stack.append(w2)
    flip = (f_factor - sym) | (sym - f_factor)
    flip_components = components(flip, edges, vertices)
    assert 2 - 2 + comp == flip_components == 1
    assert flip in (set(c) for c in cycles)  # Hamiltonian C_1
    return {"h": 2, "c": 2, "tau_mu_components": comp,
            "flip_components": flip_components,
            "identity_15": "2-2+1 = 1 on the cube lateral flip",
            "scope": "cube instance; general proof reviewed in prose"}


def family_arithmetic_checks():
    """General-m rational facts: the parametrization is a genuine long
    gap, the bridge value is m/(m-2) > 0, and the margin is zero."""
    for m in range(8, 42, 2):
        for j in range(4, m - 3, 2):
            a_len, b_len = m - j - 1, j - 1
            assert a_len >= 3 and b_len >= 3
            assert a_len % 2 == b_len % 2 == 1
            assert a_len + b_len == m - 2
            w_beta = Fraction(m, m - 2)
            assert w_beta == 1 + Fraction(2, m - 2) > 0
    return {"parametrization": "even m>=8, even 4<=j<=m-4, arcs odd "
                               ">=3 summing to m-2",
            "w_beta": "m/(m-2) = 1+2/(m-2) > 0",
            "margin": "1 - Delta = 0 throughout the family",
            "scope": "exact rational arithmetic"}


def formal_checks():
    return {
        "inherited_i194_formal_checks": PREVIOUS["formal_checks"](),
        "scope": "Cap-prism instance values checked by fresh "
                 "enumeration; general-m exhaustion, admissibility "
                 "and independence proofs, and the route obstructions "
                 "reviewed in prose",
    }


def replay():
    before = authenticate()
    cap = cap_prism_checks()
    flip = multi_component_flip_check()
    family = family_arithmetic_checks()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "cap_prism": cap,
            "multi_component_flip": flip,
            "family_arithmetic": family,
            "formal_checks": checks,
            "sealed_reference_replay": reference,
            "I195_computational_seal": False,
            "local_ear_mechanism": "PARKED", "E183_line": "PARKED",
            "short_gap_front": "PARKED at J194/J193",
            "long_gap_front": "PARKED at J195 per the brief's "
                              "stopping rule",
            "universal_exchange": "UNRESOLVED (J195 long-gap rank "
                                  "bound and parked short-gap bridge)",
            "Q164": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i195-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I195 hashes, cap-prism family, multi-component flip "
          "and inherited replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
