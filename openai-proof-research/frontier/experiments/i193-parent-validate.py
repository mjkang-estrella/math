"""I193 byte authentication, pairing-symmetry, composition and
prism checks, and inherited replay.

The finite checks below independently verify, with fresh parent-side
enumeration and exact rational linear algebra: the complementary
pairing symmetry (7) on the prism family (both pairings of a lateral
square give alpha = -(m-3)/(m-2), lambda = 1/(m-2), m in {4,6,8}); the
A/B/T partition with all four three-edge patterns on the cube's lateral
square; and the central-square composition on the cube rung step (the
lost family is exactly the lift of the first step's D11 fibre,
Delta_c = eta, the transported coefficient lambda_c = 1/4 =
lambda/(1+2*lambda) for lambda = 1/2, and d(J) = d(H)+2 = d(G)+4-2 by
direct enumeration of the twice-expanded graph). The quotient
uniqueness arguments, the lattice parity subcase and the manuscript
scope limits are reviewed in prose (see the parent disposition).
"""
import json
import runpy
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i192-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
SOURCE = "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex"
SOURCE_HASH = "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
OUTPUTS = {
    "frontier/iterations/i193-equality-bridge.md":
        "e1402e6ec2561f35f3b6d0b5c67361afdb907652b5815134fb2215b6bcb59cb5",
    "frontier/experiments/i193_equality_bridge/analytic-attempt.md":
        "b8885c3402f1f305a339950d0a2fbcf96719d5ac0223254498ff4deb6989f2ce",
    "frontier/experiments/i193_equality_bridge/reading-and-failures.md":
        "f55cafa8361e5e2f0921d5a92b4b22797d03b34040c9e1dbc508f392a9864887",
    "frontier/experiments/i193_equality_bridge/input-authentication.json":
        "fe2dcb50c360306b834e35c7f630b0801cab8dd2a46e4069bbcab2899e00b9ba",
    "frontier/sources/i193_equality_bridge/literature.md":
        "5149730a7f269162d309deac76a1a49e4fd969443a1905df4dc9428c1687cb8d",
}
ANCHORS = {
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
_rank = PREVIOUS["_rank"]
_prism_edges = PREVIOUS["_prism_edges"]
_order = PREVIOUS["_order"]
_vec = PREVIOUS["_vec"]
_spanning_paths = PREVIOUS["_spanning_paths"]
_all_paths = PREVIOUS["_all_paths"]


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i193-equality-bridge.md"}
    for directory in ("frontier/experiments/i193_equality_bridge",
                      "frontier/sources/i193_equality_bridge"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i193_equality_bridge/input-authentication.json").read_bytes())
    assert receipt["required_anchors_all_match"] is True
    assert receipt["unsealed"] is True
    inputs = receipt["inputs"]
    assert len(inputs) == 15
    anchored = 0
    for path, digest in inputs.items():
        assert sha(path) == digest, path
        if path in ANCHORS:
            assert digest == ANCHORS[path]
            anchored += 1
    assert anchored == 5
    assert set(receipt["required_anchor_paths"]) == set(ANCHORS)
    archive = json.loads((ROOT / "frontier/iterations"
        "/iteration193-equality-bridge-task.json").read_bytes())
    assert set(archive["write_scope"]) == set(OUTPUTS)
    assert archive["anchors"]["I192_report"] == ANCHORS[
        "frontier/iterations/i192-exchange-residual.md"]
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "supplied_anchors": anchored,
            "input_records": len(inputs),
            "previous_proof_records": "unchanged"}


def _solve_one(rows, values, dim):
    """One exact solution of rows x = values, free variables zero."""
    mat = [[Fraction(a) for a in row] + [Fraction(v)]
           for row, v in zip(rows, values)]
    pivots = {}
    for row in mat:
        for col in range(dim):
            if row[col] == 0:
                continue
            if col in pivots:
                f = row[col]
                row = [a - f * b for a, b in zip(row, pivots[col])]
            else:
                pivots[col] = [a / row[col] for a in row]
                break
        else:
            assert row[dim] == 0, "inconsistent"
    x = [Fraction(0)] * dim
    for col in sorted(pivots, reverse=True):
        row = pivots[col]
        x[col] = row[dim] - sum(row[j] * x[j] for j in range(col + 1, dim))
    return x


def _functional_quotient(rows_basis, dim, r_vec):
    """w with w=0 on span(rows_basis), w(r)=1 (quotient unique)."""
    return _solve_one(list(rows_basis) + [list(r_vec)],
                      [Fraction(0)] * len(rows_basis) + [Fraction(1)], dim)


def pairing_symmetry_checks():
    """Equation (7): both pairings of one lateral square share alpha."""
    out = {}
    for m in (4, 6, 8):
        edges = _prism_edges(m)
        cycles = PREVIOUS["_hamiltonian_cycles"](m, edges)
        dim = 3 * m
        res = {}
        for tag, deleted, arcs in (
                ("rungs", (("r", 0), ("r", 1)), (("t", 0), ("b", 0))),
                ("rails", (("t", 0), ("b", 0)), (("r", 0), ("r", 1)))):
            e, f = deleted
            a, ap = arcs
            def uses(c, name):
                return name in c
            lost = [c for c in cycles if e not in c and f not in c]
            survivors = [c for c in cycles if c not in lost]
            assert lost
            s_base = _vec(survivors[0], m)
            lv_rows = [[x - y for x, y in zip(_vec(c, m), s_base)]
                       for c in survivors[1:]]
            lv_rows += [[x - y for x, y in zip(_vec(c, m), _vec(lost[0], m))]
                        for c in lost[1:]]
            r_vec = [x - y for x, y in zip(_vec(lost[0], m), s_base)]
            # s_pairing = e + f - a - a'
            s_vec = [Fraction(0)] * dim
            for name, val in ((e, 1), (f, 1), (a, -1), (ap, -1)):
                s_vec[_order(m).index(name)] = val
            w = _functional_quotient(lv_rows, dim, r_vec)
            alpha = sum(wi * si for wi, si in zip(w, s_vec))
            lam = 1 + alpha
            assert lam == Fraction(1, m - 2), (m, tag, lam)
            res[tag] = {"alpha": str(alpha), "lambda": str(lam),
                        "lost": len(lost)}
        assert res["rungs"]["alpha"] == res["rails"]["alpha"]
        out[m] = res
    return {"symmetry_7": "alpha_A == alpha_B on the prism family",
            "per_m": out,
            "scope": "m in {4,6,8} exact rational quotient functionals; "
                     "general symmetry proof reviewed in prose"}


def _generic_cycles(vertices, edge_list, start=None):
    adj = {}
    for idx, (a, b) in enumerate(edge_list):
        adj.setdefault(a, []).append((b, idx))
        adj.setdefault(b, []).append((a, idx))
    if start is None:
        start = min(vertices)
    found = set()

    def dfs(path, used):
        u = path[-1]
        for w, idx in adj[u]:
            if w == start and len(path) == len(vertices):
                found.add(frozenset(used) | {idx})
            elif w not in path:
                dfs(path + [w], used | {idx})
    dfs([start], frozenset())
    return found


def _generic_rank(cycles, n_edges):
    cycles = sorted(cycles, key=lambda c: sorted(c))
    base = cycles[0]

    def vec(c):
        return [1 if i in c else 0 for i in range(n_edges)]
    return _rank([[a - b for a, b in zip(vec(c), vec(base))]
                  for c in cycles[1:]], n_edges), vec


def composition_checks():
    """Central-square composition on the cube rung step: (9), (11),
    the lost-fibre bijection, the A/B/T partition, and d(J)."""
    m = 4
    edges = _prism_edges(m)
    cycles = sorted(PREVIOUS["_hamiltonian_cycles"](m, edges),
                    key=lambda c: sorted(c))
    n_e = 3 * m
    d_g, vec_g = _generic_rank(
        {frozenset(_order(m).index(e) for e in c) for c in cycles}, n_e)
    assert d_g == 5
    u, v, x, y = (0, 0), (1, 0), (0, 1), (1, 1)
    e_name, f_name = ("r", 0), ("r", 1)
    a_name, ap_name = ("t", 0), ("b", 0)
    # A/B/T partition on the lateral square.
    square = {e_name, f_name, a_name, ap_name}
    cls_a = [c for c in cycles if not c & {e_name, f_name}]
    cls_b = [c for c in cycles if not c & {a_name, ap_name}]
    cls_t = [c for c in cycles if len(c & square) == 3]
    assert len(cls_a) == 1 and len(cls_b) == 1 and len(cls_t) == 4
    assert len({frozenset(square - c) for c in cls_t}) == 4
    assert all(len(c & square) == 2 for c in cls_a + cls_b)
    assert not [c for c in cycles if len(c & square) not in (2, 3)]
    # Build H: delete rungs rho_0,rho_1; arms + square on p,q,r,s.
    old_edges = {k: val for k, val in edges.items()
                 if k not in (e_name, f_name)}
    h_edges = list(old_edges.values())
    names_h = list(old_edges)
    for nm, ends in (("up", (u, "p")), ("vq", (v, "q")),
                     ("xr", (x, "r")), ("ys", (y, "s")),
                     ("pq", ("p", "q")), ("qs", ("q", "s")),
                     ("sr", ("s", "r")), ("rp", ("r", "p"))):
        names_h.append(nm)
        h_edges.append(ends)
    h_index = {nm: i for i, nm in enumerate(names_h)}
    h_vertices = {w for pair in h_edges for w in pair}
    h_cycles = _generic_cycles(h_vertices, h_edges, start=(0, 0))
    d_h, _ = _generic_rank(h_cycles, len(h_edges))
    assert d_h == d_g + 2 == 7
    # First-step D11 fibre (in K) and its lifts in H.
    adj_k = {}
    for a2, b2 in old_edges.values():
        adj_k.setdefault(a2, []).append(b2)
        adj_k.setdefault(b2, []).append(a2)
    verts_k = frozenset(adj_k)
    edge_of_k = {frozenset(val): k for k, val in old_edges.items()}

    def k_path_edges(path):
        return frozenset(edge_of_k[frozenset((a2, b2))]
                         for a2, b2 in zip(path, path[1:]))

    d11 = []
    for p in _all_paths(adj_k, u, v):
        rest = verts_k - set(p)
        if x not in rest or y not in rest:
            continue
        sub = {w: [z2 for z2 in adj_k[w] if z2 in rest] for w in rest}
        d11.extend(k_path_edges(p) | k_path_edges(q)
                   for q in _spanning_paths(sub, rest, x, y))
    assert len(d11) == 1
    arm_sq = {"up", "vq", "xr", "ys", "rp", "qs"}
    lifts = {frozenset(h_index[nm] for nm in
                       [*_k_names(d, old_edges), *arm_sq])
             for d in d11}
    # Central step: delete pq, rs from H.
    lost_c = {c for c in h_cycles
              if h_index["pq"] not in c and h_index["sr"] not in c}
    assert lost_c == lifts
    survivors_c = [c for c in h_cycles if c not in lost_c]
    s0 = survivors_c[0]

    def vh(c):
        return [1 if i in c else 0 for i in range(len(h_edges))]

    base_s = vh(s0)
    l_rows = [[a2 - b2 for a2, b2 in zip(vh(c), base_s)]
              for c in survivors_c[1:]]
    dim_l = _rank(l_rows, len(h_edges))
    ell_c = d_h - dim_l
    # U_c in K' = H - {pq, sr}: spanning p-r paths, q-s paths, and
    # (p,q)+(r,s) two-path covers.
    adj_kp = {}
    for i, (a2, b2) in enumerate(h_edges):
        if names_h[i] in ("pq", "sr"):
            continue
        adj_kp.setdefault(a2, []).append((b2, i))
        adj_kp.setdefault(b2, []).append((a2, i))
    adj_simple = {w: [z2 for z2, _ in nbrs] for w, nbrs in adj_kp.items()}
    verts_kp = frozenset(adj_simple)

    def kp_paths(src, dst):
        out = []
        for p in _spanning_paths(adj_simple, verts_kp, src, dst):
            es = []
            for a2, b2 in zip(p, p[1:]):
                es.append(next(i for z2, i in adj_kp[a2]
                               if z2 == b2))
            out.append(es)
        return out

    p_pr = kp_paths("p", "r")
    p_qs = kp_paths("q", "s")
    dd = []
    for p in _all_paths(adj_simple, "p", "q"):
        rest = verts_kp - set(p)
        if "r" not in rest or "s" not in rest:
            continue
        sub = {w: [z2 for z2 in adj_simple[w] if z2 in rest]
               for w in rest}
        pes = []
        for a2, b2 in zip(p, p[1:]):
            pes.append(next(i for z2, i in adj_kp[a2] if z2 == b2))
        for q2 in _spanning_paths(sub, rest, "r", "s"):
            qes = []
            for a2, b2 in zip(q2, q2[1:]):
                qes.append(next(i for z2, i in adj_kp[a2] if z2 == b2))
            dd.append(pes + qes)
    assert p_pr and p_qs and dd

    def rows_of(fams):
        if len(fams) <= 1:
            return []
        base = fams[0]

        def vv(f):
            return [1 if i in f else 0 for i in range(len(h_edges))]
        return [[a2 - b2 for a2, b2 in zip(vv(f), vv(base))]
                for f in fams[1:]]
    u_rows = rows_of(p_pr) + rows_of(p_qs) + rows_of(dd)
    t_c = _rank(l_rows + u_rows, len(h_edges)) - dim_l
    prev_receipt = json.loads(
        (EXP / "i192-parent-verification.json").read_bytes())
    eta_first = prev_receipt["prism_verification"]["prisms"]["4"]["rungs"]["eta"]
    assert eta_first == 1
    assert ell_c == 1 and t_c == 0
    assert ell_c - t_c == eta_first  # (9): Delta_c = eta
    # lambda_c: s_c = pq + rs - pr - qs; r_c = lost - survivor base.
    s_c = [Fraction(0)] * len(h_edges)
    for nm, val in (("pq", 1), ("sr", 1), ("rp", -1), ("qs", -1)):
        s_c[h_index[nm]] = val
    # degree-zero check (alternating square)
    for vtx in h_vertices:
        tot = sum(s_c[i] for i, (a2, b2) in enumerate(h_edges)
                  if vtx in (a2, b2))
        assert tot == 0
    r_c = [a2 - b2 for a2, b2 in zip(vh(next(iter(lost_c))), base_s)]
    w_c = _functional_quotient(l_rows, len(h_edges), r_c)
    alpha_c = sum(wi * si for wi, si in zip(w_c, s_c))
    lam_c = 1 + alpha_c
    lam = Fraction(1, 2)
    assert lam_c == lam / (1 + 2 * lam) == Fraction(1, 4)  # (11)
    # Twice-expanded graph J: expand the central square again.
    j_edges = [(a2, b2) for nm, (a2, b2) in zip(names_h, h_edges)
               if nm not in ("pq", "sr")]
    for a2, b2 in (("p", "p2"), ("q", "q2"), ("r", "r2"), ("s", "s2"),
                   ("p2", "q2"), ("q2", "s2"), ("s2", "r2"), ("r2", "p2")):
        j_edges.append((a2, b2))
    j_vertices = {w for pair in j_edges for w in pair}
    j_cycles = _generic_cycles(j_vertices, j_edges, start=(0, 0))
    d_j, _ = _generic_rank(j_cycles, len(j_edges))
    assert d_j == d_h + 2 == 9
    return {"d_G": d_g, "d_H": d_h, "d_J": d_j,
            "lost_equals_D11_lift": True, "D11_size": len(d11),
            "Delta_c": ell_c - t_c, "eta_first": eta_first,
            "lambda": str(lam), "lambda_c": str(lam_c),
            "ABT_partition": {"A": 1, "B": 1, "T": 4,
                              "three_edge_patterns": 4},
            "scope": "Cube rung step and its central successor, exact "
                     "enumeration and rational ranks; general proofs "
                     "reviewed in prose"}


def _k_names(d, old_edges):
    return [k for k in old_edges if k in d]


def formal_checks():
    return {
        "inherited_i192_formal_checks": PREVIOUS["formal_checks"](),
        "scope": "Pairing symmetry and composition identities checked "
                 "on exact instances; quotient uniqueness, lattice "
                 "parity and manuscript scope reviewed in prose",
    }


def replay():
    before = authenticate()
    symmetry = pairing_symmetry_checks()
    composition = composition_checks()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "pairing_symmetry": symmetry,
            "central_composition": composition,
            "formal_checks": checks,
            "sealed_reference_replay": reference,
            "I193_computational_seal": False,
            "local_ear_mechanism": "PARKED", "E183_line": "PARKED",
            "short_gap_exchange": "UNRESOLVED at J193",
            "universal_exchange": "UNRESOLVED at J192",
            "Q164": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i193-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I193 hashes, pairing symmetry, central composition "
          "and inherited replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
