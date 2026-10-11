"""I192 byte authentication, matching-lemma, prism and bridge checks,
and inherited replay.

The finite checks below independently verify, with fresh parent-side
enumeration and exact rational rank computations: the noncrossing
matching lemma behind the facial-translation classification (for
m = 1..8 the unique noncrossing even-odd pairing whose union with the
selected matching is one cycle is the shifted pairing); the prism
exhaustion (exactly m+2 Hamiltonian cycles, two-rung C_i structure,
alternating twisted pair, affine independence, identity (17),
lost/survivor sets, and ell, t, eta by direct enumeration and rank
computation for m in {4,6,8} on both deletion types); and the bridge
identity (10). The Delta bookkeeping, equality-case analysis (13), and
I178 scoping are reviewed in prose (see the parent disposition).
"""
import json
import runpy
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i191-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
SOURCE = "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex"
SOURCE_HASH = "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
OUTPUTS = {
    "frontier/iterations/i192-exchange-residual.md":
        "ffc58919a1ce84f086e36e7b7b85c803dbd47c0dd7609046fc44711aa14c126d",
    "frontier/experiments/i192_exchange_residual/analytic-attempt.md":
        "b5cd998c37546f7ad1255aa6361e6fbbd63ba616b8ff8e15872bdad2e93eee38",
    "frontier/experiments/i192_exchange_residual/reading-and-failures.md":
        "d0dc5a5a42621cfc78f1dcc45fabb02cde4aea8e65c7f4ada50626d0ae6c8d86",
    "frontier/experiments/i192_exchange_residual/input-authentication.json":
        "fc0ce9f9ca4aa2fee1ccff208484f7842a27e20f43db492e21b10cf188728d29",
    "frontier/sources/i192_exchange_residual/literature.md":
        "19232ed4bc48fb641ddb200472811f51900b99577e6d1be34e747806fd5ec6bf",
}
ANCHORS = {
    "frontier/iterations/i168-cross-class-exchange.md":
        "696a15a676ba0ecd6e90cb196673c3d21e2f8450755113c7ee1a70d6c285db31",
    "frontier/iterations/i169-bridge-independence.md":
        "1b36713181c4f3f5b2ea6f084558dca6553bf86a7b863bfca867fee126f17fcf",
    "frontier/iterations/i170-quadrilateral-coefficient.md":
        "8345e1d12991cc328a5910e735c6d0fa625f27715b50bbd91af9917974c74096",
    "frontier/iterations/i178-five-port-annihilator.md":
        "77bbc27865e326b5b5e2eebd52f61437683b260feb82c6ed811b14216c2bdc78",
    SOURCE: SOURCE_HASH,
}


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i192-exchange-residual.md"}
    for directory in ("frontier/experiments/i192_exchange_residual",
                      "frontier/sources/i192_exchange_residual"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i192_exchange_residual/input-authentication.json").read_bytes())
    assert set(receipt["writes"]) == set(OUTPUTS)
    assert receipt["sealed_replay"] is False
    anchored = 0
    for row in receipt["anchors"]:
        assert row["matches_brief"] is True, row["path"]
        assert sha(row["path"]) == row["sha256"] == ANCHORS[row["path"]], row["path"]
        anchored += 1
    assert anchored == 5
    assert len(receipt["additional_inputs"]) == 13
    for row in receipt["additional_inputs"]:
        assert sha(row["path"]) == row["sha256"], row["path"]
    archive = json.loads((ROOT / "frontier/iterations"
        "/iteration192-exchange-residual-task.json").read_bytes())
    assert set(archive["write_scope"]) == set(OUTPUTS)
    assert archive["anchors"]["I168_report"] == ANCHORS[
        "frontier/iterations/i168-cross-class-exchange.md"]
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "supplied_anchors": anchored,
            "additional_inputs": len(receipt["additional_inputs"]),
            "previous_proof_records": "unchanged"}


def matching_lemma_checks():
    """Noncrossing-matching core of the facial classification (4)."""

    def gen(pts):
        if not pts:
            yield []
            return
        p0 = pts[0]
        for j in range(1, len(pts), 2):
            for inside in gen(pts[1:j]):
                for outside in gen(pts[j + 1:]):
                    yield [(p0, pts[j])] + inside + outside

    def single_cycle(matching, m):
        edges = [(2 * i, 2 * i + 1) for i in range(m)] + list(matching)
        deg = {i: 0 for i in range(2 * m)}
        adj = {i: [] for i in range(2 * m)}
        for a, b in edges:
            deg[a] += 1
            deg[b] += 1
            adj[a].append(b)
            adj[b].append(a)
        if any(deg[v] != 2 for v in deg):
            return False
        seen, stack = {0}, [0]
        while stack:
            for w in adj[stack.pop()]:
                if w not in seen:
                    seen.add(w)
                    stack.append(w)
        return len(seen) == 2 * m

    checked = {}
    for m in range(1, 9):
        expected = frozenset(tuple(sorted((2 * i + 1, (2 * i + 2) % (2 * m))))
                             for i in range(m))
        winners = []
        parity_only = 0
        for matching in gen(list(range(2 * m))):
            if any(a % 2 == b % 2 for a, b in matching):
                continue
            parity_only += 1
            if single_cycle(matching, m):
                winners.append(frozenset(matching))
        assert winners == [expected], (m, winners)
        checked[m] = {"noncrossing_even_odd": parity_only,
                      "single_cycle_survivors": 1}
    return {"m_range": [1, 8], "per_m": checked,
            "conclusion": "unique pairing (1,2),(3,4),...,(2m-1,0)",
            "scope": "Combinatorial core for m<=8; the general proof "
                     "is reviewed in prose"}


def _rank(vectors, dim):
    basis = {}
    for vec in vectors:
        row = [Fraction(x) for x in vec]
        for col in range(dim):
            if row[col] == 0:
                continue
            if col in basis:
                factor = row[col]
                pivot = basis[col]
                row = [a - factor * b for a, b in zip(row, pivot)]
            else:
                basis[col] = [a / row[col] for a in row]
                break
    return len(basis)


def _prism_edges(m):
    edges = {}
    for i in range(m):
        edges[("r", i)] = ((0, i), (1, i))
        edges[("t", i)] = ((0, i), (0, (i + 1) % m))
        edges[("b", i)] = ((1, i), (1, (i + 1) % m))
    return edges


def _order(m):
    return ([("r", i) for i in range(m)] + [("t", i) for i in range(m)]
            + [("b", i) for i in range(m)])


def _vec(edge_names, m):
    s = set(edge_names)
    return [1 if e in s else 0 for e in _order(m)]


def _hamiltonian_cycles(m, edges):
    adj = {}
    for a, b in edges.values():
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    edge_of = {frozenset(v): k for k, v in edges.items()}
    start, found = (0, 0), set()

    def dfs(path):
        u = path[-1]
        for w in adj[u]:
            if w == start and len(path) == 2 * m:
                found.add(frozenset(edge_of[frozenset((a, b))]
                                    for a, b in zip(path, path[1:])
                                    ) | {edge_of[frozenset((u, start))]})
            elif w not in path:
                dfs(path + [w])
    dfs([start])
    return sorted(found, key=lambda c: sorted(c))


def _spanning_paths(adj, vertices, src, dst):
    return [p for p in _all_paths(adj, src, dst)
            if set(p) == vertices]


def _all_paths(adj, src, dst):
    paths = []

    def dfs(path, seen):
        u = path[-1]
        if u == dst:
            paths.append(tuple(path))
            return
        for w in adj[u]:
            if w not in seen:
                dfs(path + [w], seen | {w})
    dfs([src], {src})
    return paths


def prism_checks():
    report = {}
    for m in (4, 6, 8):
        edges = _prism_edges(m)
        cycles = _hamiltonian_cycles(m, edges)
        assert len(cycles) == m + 2, (m, len(cycles))
        by_rungs = {}
        for c in cycles:
            n = sum(1 for e in c if e[0] == "r")
            by_rungs.setdefault(n, []).append(c)
        assert set(by_rungs) == {2, m}
        assert len(by_rungs[2]) == m and len(by_rungs[m]) == 2
        ordinary = {}
        for c in by_rungs[2]:
            rungs = sorted(e[1] for e in c if e[0] == "r")
            assert (rungs[1] - rungs[0]) % m in (1, m - 1)
            i0 = rungs[0] if (rungs[0] + 1) % m == rungs[1] else rungs[1]
            missing = {("t", i) for i in range(m) if ("t", i) not in c} | \
                      {("b", i) for i in range(m) if ("b", i) not in c}
            assert missing == {("t", i0), ("b", i0)}
            ordinary[i0] = c
        # Twisted pair: each layer uses an alternating rail matching and
        # the two layer choices are unequal.
        layer_matchings = []
        for c in by_rungs[m]:
            top = frozenset(e[1] for e in c if e[0] == "t")
            bottom = frozenset(e[1] for e in c if e[0] == "b")
            for layer in (top, bottom):
                assert len(layer) == m // 2
                assert all(((i + 1) % m not in layer) for i in layer)
            layer_matchings.append((top, bottom))
        assert layer_matchings[0][0] != layer_matchings[0][1]
        assert len({tuple(sorted(x)) for pair in layer_matchings
                    for x in pair}) == 2
        # Affine independence of the m+2 cycles: d(G) = m+1.
        base = _vec(cycles[0], m)
        assert _rank([[a - b for a, b in zip(_vec(c, m), base)]
                      for c in cycles[1:]], 3 * m) == m + 1
        # Identity (17): (m-2)(rho_0+rho_1-t_0-b_0)
        #   = (m-3)C_0 - sum_{j!=0} C_j + X + Y.
        lhs = [0] * (3 * m)
        for name, val in ((("r", 0), m - 2), (("r", 1), m - 2),
                          (("t", 0), -(m - 2)), (("b", 0), -(m - 2))):
            lhs[_order(m).index(name)] = val
        rhs = [(m - 3) * a for a in _vec(ordinary[0], m)]
        for j in range(1, m):
            rhs = [a - b for a, b in zip(rhs, _vec(ordinary[j], m))]
        for c in by_rungs[m]:
            rhs = [a + b for a, b in zip(rhs, _vec(c, m))]
        assert lhs == rhs, m
        alpha = Fraction(-(m - 3), m - 2)
        assert 3 + 2 * alpha == Fraction(m, m - 2) > 0
        row = {"cycles": m + 2, "affine_rank": m + 1,
               "identity_17": True, "alpha": str(alpha),
               "alpha_is_short_gap_failure": alpha == Fraction(-3, 2)}
        assert not row["alpha_is_short_gap_failure"]
        for tag, removed, u, v, x, y in (
                ("rungs", frozenset((("r", 0), ("r", 1))),
                 (0, 0), (1, 0), (0, 1), (1, 1)),
                ("rails", frozenset((("t", 0), ("b", 0))),
                 (0, 0), (0, 1), (1, 0), (1, 1))):
            sig = {}
            for c in cycles:
                k = tuple(int(e in c) for e in sorted(removed))
                sig.setdefault(k, []).append(c)
            lost = sig.get((0, 0), [])
            survivors = [c for ij, cs in sig.items() if ij != (0, 0)
                         for c in cs]
            if tag == "rungs":
                lost_index = sorted(
                    next(i for i in range(m)
                         if {("t", i), ("b", i)} & set(c) == set()
                         and sum(1 for e in c if e[0] == "r") == 2)
                    for c in lost)
                assert lost_index == list(range(2, m - 1)), (m, lost_index)
                assert {next(i for i in range(m)
                             if {("t", i), ("b", i)} & set(c) == set()
                             and sum(1 for e in c if e[0] == "r") == 2)
                        for c in survivors
                        if sum(1 for e in c if e[0] == "r") == 2
                        } == {0, 1, m - 1}
                expected = (m - 3, m - 4)
            else:
                assert lost == [ordinary[0]]
                expected = (1, 0)
            assert sig.get((1, 0)) and sig.get((0, 1)) and sig.get((1, 1))
            s_base = _vec(survivors[0], m)
            dim_l = _rank([[a - b for a, b in zip(_vec(c, m), s_base)]
                           for c in survivors[1:]], 3 * m)
            ell = (m + 1) - dim_l
            assert ell == expected[0], (m, tag, ell)
            t_val, eta_val, counts = _rank_t_eta(
                m, edges, removed, u, v, x, y, cycles, cycles[0], sig)
            assert (t_val, eta_val) == (expected[1], 1), \
                (m, tag, t_val, eta_val)
            row[tag] = {"lost": len(lost), "ell": ell, "t": t_val,
                        "eta": eta_val, "family_sizes": counts}
        report[m] = row
    return {"prisms": report,
            "scope": "m in {4,6,8} full enumeration and rational ranks; "
                     "general-m proof reviewed in prose"}


def _rank_t_eta(m, all_edges, removed, u, v, x, y, cycles, c0_cycle, sig):
    edges = {k: val for k, val in all_edges.items() if k not in removed}
    adj = {}
    for a, b in edges.values():
        adj.setdefault(a, []).append(b)
        adj.setdefault(b, []).append(a)
    edge_of = {frozenset(val): k for k, val in edges.items()}
    vertices = frozenset(adj)
    order = list(edges) + sorted(removed)

    def vec(names):
        s = set(names)
        return [1 if e in s else 0 for e in order]

    def path_edges(path):
        return [edge_of[frozenset((a, b))]
                for a, b in zip(path, path[1:])]

    p_ux = [path_edges(p) for p in _spanning_paths(adj, vertices, u, x)]
    p_vy = [path_edges(p) for p in _spanning_paths(adj, vertices, v, y)]
    d_11 = []
    for p in _all_paths(adj, u, v):
        rest = vertices - set(p)
        if x not in rest or y not in rest:
            continue
        sub_adj = {w: [z for z in adj[w] if z in rest] for w in rest}
        d_11.extend(path_edges(p) + path_edges(q)
                    for q in _spanning_paths(sub_adj, rest, x, y))
    assert p_ux and p_vy and d_11

    def diff_rows(families):
        if len(families) <= 1:
            return []
        base = vec(families[0])
        return [[a - b for a, b in zip(vec(f), base)]
                for f in families[1:]]

    survivors = [c for ij, cs in sig.items() if ij != (0, 0) for c in cs]
    s0 = survivors[0]
    l_rows = [[a - b for a, b in zip(vec(c), vec(s0))]
              for c in survivors if c != s0]
    dim_l = _rank(l_rows, len(order))
    u_rows = diff_rows(p_ux) + diff_rows(p_vy) + diff_rows(d_11)
    dim_lu = _rank(l_rows + u_rows, len(order))
    t = dim_lu - dim_l
    b_vec = [pi + qi + di - 3 * ci for pi, qi, di, ci
             in zip(vec(p_ux[0]), vec(p_vy[0]), vec(d_11[0]), vec(s0))]
    for name in removed:
        b_vec[order.index(name)] += 2
    eta = _rank(l_rows + u_rows + [b_vec], len(order)) - dim_lu
    return t, eta, {"Pux": len(p_ux), "Pvy": len(p_vy), "D11": len(d_11)}


def bridge_identity_check():
    """Pure vector identity (10): b = 3r + 2 s_arc + a_P + a_Q + a_D."""
    syms = ["P", "Q", "D", "N", "C0", "e", "f", "qA", "qB"]

    def v(**kw):
        return [Fraction(kw.get(s, 0)) for s in syms]
    b = v(P=1, Q=1, D=1, e=2, f=2, C0=-3)
    rhs = [3 * ri + 2 * si + api + aqi + adi
           for ri, si, api, aqi, adi in zip(
               v(N=1, C0=-1), v(e=1, f=1, qA=-1, qB=-1),
               v(P=1, qA=1, N=-1), v(Q=1, qB=1, N=-1),
               v(D=1, qA=1, qB=1, N=-1))]
    assert rhs == b
    return {"identity_10": True}


def formal_checks():
    return {
        "inherited_i191_formal_checks": PREVIOUS["formal_checks"](),
        "scope": "Matching lemma, prism exhaustion/ranks and bridge "
                 "identity are finite checks; Delta bookkeeping, "
                 "equality case (13) and I178 scoping reviewed in prose",
    }


def replay():
    before = authenticate()
    lemma = matching_lemma_checks()
    prisms = prism_checks()
    bridge = bridge_identity_check()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "matching_lemma": lemma, "prism_verification": prisms,
            "bridge_identity": bridge, "formal_checks": checks,
            "sealed_reference_replay": reference,
            "I192_computational_seal": False,
            "local_ear_mechanism": "PARKED", "E183_line": "PARKED",
            "universal_exchange": "UNRESOLVED at J192",
            "Q164": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i192-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I192 hashes, matching lemma, prism verification, "
          "bridge identity and inherited replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
