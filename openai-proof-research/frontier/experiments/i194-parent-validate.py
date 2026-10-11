"""I194 byte authentication, cube flip-obstruction, fractional
exclusion, block-cover and matching-bookkeeping checks, and inherited
replay.

The finite checks below independently verify, with fresh parent-side
enumeration and exact rational linear algebra on the cube rail-deletion
step (child of the cube is the C6 prism): the complete six-cycle old
family and N00 = {C_0}; the canonical two-factor F as exactly the two
layer squares; the written identity (10) as an integer vector equality;
the quotient value lambda = w(F - C*) = 1/2 and w(s) = -1/2; the claim
that for EVERY surviving cycle C the symmetric difference F Delta C is
a single simple alternating cycle (the lateral squares for C_1..C_3,
the edge set of Y for X and conversely) whose only flip is the
disconnected F; the flip criterion (5) on the q = 2 instance
(beta = tau, two components, matching the component count of F); the
three-matching bookkeeping (13)/(14) on the cube (M0 = all rungs, the
opposite phase gives the Hamiltonian pair {X, Y} with h-sum 0, the
same phase gives disconnected unions, kappa = w(2E - 3C*) = 1/2); the
prism fractional-value exclusion of integral certificates
(lambda = 1/(m-2) is never integral for even m >= 4); the central
recurrence lambda_j = lambda/(1 + 2j lambda); the negative-iterate
hitting condition (the orbit of -p/q reaches -1/2 exactly when
2p divides q); and the coefficient-cover counting behind (7)/(8).
The flip criterion's general proof, the conditional block lemma, the
phase-incompatibility argument and the manuscript scope limits are
reviewed in prose (see the parent disposition).
"""
import itertools
import json
import runpy
import sys
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i193-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
SOURCE = "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex"
SOURCE_HASH = "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
OUTPUTS = {
    "frontier/iterations/i194-quotient-sign.md":
        "21f8e32eec69b89d7e6eade2763a3f7b125c6575121f5f05bddb0d37ab21b2b2",
    "frontier/experiments/i194_quotient_sign/analytic-attempt.md":
        "cbefcb56c4d3370a49aba50177fd596349beba2ed70810061465fb750d615bef",
    "frontier/experiments/i194_quotient_sign/reading-and-failures.md":
        "0cf6abdb7783470756a5aea2d11e93b1e2fd1c5273c2c20f1c79cc4d3575b73f",
    "frontier/experiments/i194_quotient_sign/input-authentication.json":
        "89477945bd10991ce4414d29bde5b031d1e945d777cf6a5ffe4e6cd58d8d8db3",
    "frontier/sources/i194_quotient_sign/literature.md":
        "7a3c5d206e43e2ede0e893dddd29cf5d981effd8e4fc080e95c37575a0a24489",
}
ANCHORS = {
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
_rank = PREVIOUS["_rank"]
_prism_edges = PREVIOUS["_prism_edges"]
_order = PREVIOUS["_order"]
_vec = PREVIOUS["_vec"]
_functional_quotient = PREVIOUS["_functional_quotient"]


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i194-quotient-sign.md"}
    for directory in ("frontier/experiments/i194_quotient_sign",
                      "frontier/sources/i194_quotient_sign"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i194_quotient_sign/input-authentication.json").read_bytes())
    assert receipt["status"].startswith("COMPLETE authentication")
    assert "unsealed" in receipt["record_type"]
    assert receipt["pinned_revision"] == (
        "fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb")
    assert receipt["required_anchors_all_match"] is True
    anchored = 0
    for row in receipt["required_anchors"]:
        assert row["matches_brief"] is True, row["path"]
        assert sha(row["path"]) == row["sha256"] == ANCHORS[row["path"]], row["path"]
        anchored += 1
    assert anchored == 6
    assert len(receipt["additional_inputs"]) == 12
    for row in receipt["additional_inputs"]:
        assert sha(row["path"]) == row["sha256"], row["path"]
    archive = json.loads((ROOT / "frontier/iterations"
        "/iteration194-quotient-sign-task.json").read_bytes())
    assert set(archive["write_scope"]) == set(OUTPUTS)
    assert archive["anchors"]["I193_report"] == ANCHORS[
        "frontier/iterations/i193-equality-bridge.md"]
    assert archive["anchors"]["I192_report"] == ANCHORS[
        "frontier/iterations/i192-exchange-residual.md"]
    assert "PARKED" in archive["stopping_rule"]
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "supplied_anchors": anchored,
            "additional_inputs": len(receipt["additional_inputs"]),
            "previous_proof_records": "unchanged"}


def _components(edge_names, edges, vertices):
    adj = {v: [] for v in vertices}
    for name in edge_names:
        a, b = edges[name]
        adj[a].append(b)
        adj[b].append(a)
    seen, count = set(), 0
    for v in vertices:
        if adj[v] and v not in seen:
            count += 1
            stack = [v]
            seen.add(v)
            while stack:
                for w in adj[stack.pop()]:
                    if w not in seen:
                        seen.add(w)
                        stack.append(w)
    return count


def cube_flip_checks():
    """Cube rail-deletion step: F, identity (10), lambda = 1/2, the
    single-alternating-cycle obstruction, criterion (5), and the
    three-matching bookkeeping (13)/(14)."""
    m = 4
    edges = _prism_edges(m)
    cycles = PREVIOUS["PREVIOUS"]["_hamiltonian_cycles"](m, edges)
    assert len(cycles) == 6
    dim = 3 * m
    vertices = [(layer, i) for layer in (0, 1) for i in range(m)]
    e, f = ("t", 0), ("b", 0)
    a, ap = ("r", 0), ("r", 1)
    lost = [c for c in cycles if e not in c and f not in c]
    assert len(lost) == 1
    c0 = lost[0]
    survivors = [c for c in cycles if c != c0]
    assert len(survivors) == 5
    twisted = [c for c in survivors
               if all(("r", i) in c for i in range(m))]
    assert len(twisted) == 2
    x_cyc, y_cyc = twisted
    lateral = {}
    for i in range(1, m):
        match = [c for c in survivors
                 if ("t", i) not in c and ("b", i) not in c]
        assert len(match) == 1
        lateral[i] = match[0]
    assert set(lateral.values()) | set(twisted) == set(survivors)
    # Canonical two-factor: Q = C_0 - rho_1, F = Q - rho_0 + t_0 + b_0.
    q_edges = set(c0) - {ap}
    f_factor = (q_edges - {a}) | {e, f}
    rails = {("t", i) for i in range(m)} | {("b", i) for i in range(m)}
    assert f_factor == rails
    assert _components(f_factor, edges, vertices) == 2
    deg = {v: 0 for v in vertices}
    for name in f_factor:
        for w in edges[name]:
            deg[w] += 1
    assert all(deg[v] == 2 for v in vertices)  # spanning two-factor
    # Quotient functional: W' = L (V = U = 0 on this step), w(r) = 1.
    base = _vec(lateral[1], m)  # surviving base C* = C_1
    l_rows = [[x_ - y_ for x_, y_ in zip(_vec(c, m), base)]
              for c in survivors if c != lateral[1]]
    assert _rank(l_rows, dim) == 4
    assert _rank(l_rows + [[x_ - y_ for x_, y_ in
                            zip(_vec(c0, m), base)]], dim) == 5
    r_vec = [x_ - y_ for x_, y_ in zip(_vec(c0, m), base)]
    w = _functional_quotient(l_rows, dim, r_vec)

    def apply_w(names_vec):
        return sum(wi * Fraction(vi) for wi, vi in zip(w, names_vec))
    # w has affine value 0 on survivors and 1 on the lost cycle.
    for c in survivors:
        assert apply_w([x_ - y_ for x_, y_ in zip(_vec(c, m), base)]) == 0
    assert apply_w(r_vec) == 1
    # s = t_0 + b_0 - rho_0 - rho_1; w(s) = -1/2.
    s_vec = [0] * dim
    for name, val in ((e, 1), (f, 1), (a, -1), (ap, -1)):
        s_vec[_order(m).index(name)] = val
    assert apply_w(s_vec) == Fraction(-1, 2)
    # z = F - C*; lambda = w(z) = 1/2.
    z_vec = [x_ - y_ for x_, y_ in zip(_vec(f_factor, m), base)]
    lam = apply_w(z_vec)
    assert lam == Fraction(1, 2)
    # Identity (10): 2(rho_0+rho_1-t_0-b_0) = C_0-C_1-C_2-C_3+X+Y.
    lhs = [Fraction(-2) * v for v in s_vec]
    rhs = list(_vec(c0, m))
    for c in (lateral[1], lateral[2], lateral[3]):
        rhs = [x_ - y_ for x_, y_ in zip(rhs, _vec(c, m))]
    for c in (x_cyc, y_cyc):
        rhs = [x_ + y_ for x_, y_ in zip(rhs, _vec(c, m))]
    assert [Fraction(v) for v in rhs] == lhs
    assert sum(rhs) == 0  # zero-degree identity
    # For every surviving C, F Delta C is one simple alternating cycle.
    flip_summaries = {}
    for tag, c in ([("C1", lateral[1]), ("C2", lateral[2]),
                    ("C3", lateral[3]), ("X", x_cyc), ("Y", y_cyc)]):
        sym = set(c) ^ set(f_factor)
        # 2-regular alternating subgraph on its support.
        sup_adj = {}
        for name in sym:
            for wv in edges[name]:
                sup_adj.setdefault(wv, []).append(name)
        assert all(len(v) == 2 for v in sup_adj.values())
        for v, inc in sup_adj.items():
            in_f = [n in f_factor for n in inc]
            assert in_f == [True, False] or in_f == [False, True]
        assert _components(sym, edges, vertices) == 1
        flip = (set(c) - sym) | (sym - set(c))
        assert flip == set(f_factor)
        assert _components(flip, edges, vertices) == 2
        flip_summaries[tag] = len(sym)
    for i in (1, 2, 3):
        sym = set(lateral[i]) ^ set(f_factor)
        assert sym == {("t", i), ("b", i), ("r", i), ("r", (i + 1) % m)}
        assert flip_summaries["C%d" % i] == 4
    assert set(x_cyc) ^ set(f_factor) == set(y_cyc)
    assert set(y_cyc) ^ set(f_factor) == set(x_cyc)
    assert flip_summaries["X"] == flip_summaries["Y"] == 8
    # Criterion (5) on the lateral square R = F Delta C_1: q = 2,
    # beta = tau, and components(tau union beta) = 2 = components(F).
    c1 = lateral[1]
    sym = set(c1) ^ set(f_factor)
    removed = sym & set(c1)
    added = sym - set(c1)
    assert len(removed) == len(added) == 2
    rest = set(c1) - removed
    rest_adj = {}
    for name in rest:
        u_, v_ = edges[name]
        rest_adj.setdefault(u_, []).append(v_)
        rest_adj.setdefault(v_, []).append(u_)
    endpoints = sorted(v for v in rest_adj if len(rest_adj[v]) == 1)
    assert len(endpoints) == 4
    # Trace the two paths to get tau.
    tau = set()
    seen = set()
    for s0 in endpoints:
        if s0 in seen:
            continue
        path = [s0]
        seen.add(s0)
        while len(rest_adj[path[-1]]) == 2 or len(path) == 1:
            nxt = [w for w in rest_adj[path[-1]] if w not in path]
            if not nxt:
                break
            path.append(nxt[0])
            seen.add(nxt[0])
        tau.add(frozenset((path[0], path[-1])))
    assert len(tau) == 2
    beta = {frozenset(edges[name]) for name in added}
    assert beta == tau  # the q = 2 failure condition
    mg_adj = {}
    for pair in tau | beta:
        a_, b_ = sorted(pair)
        mg_adj.setdefault(a_, []).append(b_)
        mg_adj.setdefault(b_, []).append(a_)
    seen2, comp = set(), 0
    for v in mg_adj:
        if v not in seen2:
            comp += 1
            stack = [v]
            seen2.add(v)
            while stack:
                for w_ in mg_adj[stack.pop()]:
                    if w_ not in seen2:
                        seen2.add(w_)
                        stack.append(w_)
    assert comp == 2 == _components(f_factor, edges, vertices)
    # Three-matching bookkeeping on the cube: M0 = all rungs.
    m0 = {("r", i) for i in range(m)}
    assert m0 == set(edges) - set(f_factor)
    deg0 = {v: 0 for v in vertices}
    for name in m0:
        for wv in edges[name]:
            deg0[wv] += 1
    assert all(deg0[v] == 1 for v in vertices)  # perfect matching
    # Phase splits of F into perfect matchings M1, M2.
    phases = []
    sq_top = {("t", i) for i in range(m)}
    sq_bot = {("b", i) for i in range(m)}
    top_even = {("t", i) for i in range(m) if i % 2 == 0}
    top_odd = sq_top - top_even
    bot_even = {("b", i) for i in range(m) if i % 2 == 0}
    bot_odd = sq_bot - bot_even
    for m1 in (top_even | bot_even, top_even | bot_odd):
        m2 = set(f_factor) - m1
        phases.append((m1, m2))
    phase_rows = []
    for m1, m2 in phases:
        unions = (m0 | m1, m0 | m2)
        ham = [set(u_) in (set(x_cyc), set(y_cyc)) for u_ in unions]
        comps = [_components(u_, edges, vertices) for u_ in unions]
        # Identity (13): F + F01 + F02 = 2E as vectors.
        tot = [x_ + y_ for x_, y_ in
               zip(_vec(unions[0], m), _vec(unions[1], m))]
        tot = [x_ + y_ for x_, y_ in zip(tot, _vec(f_factor, m))]
        assert tot == [2] * dim
        phase_rows.append({"hamiltonian": ham, "components": comps})
    assert sorted(tuple(sorted(r["hamiltonian"])) for r in phase_rows) == [
        (False, False), (True, True)]
    good = next(r for r in phase_rows if all(r["hamiltonian"]))
    bad = next(r for r in phase_rows if not any(r["hamiltonian"]))
    assert bad["components"] == [2, 2]
    # Opposite phase: one union uses e only, the other f only; j = 0.
    m1g, m2g = next((m1, m2) for m1, m2 in phases
                    if set(m0 | m1) in (set(x_cyc), set(y_cyc)))
    uses = [((e in (m0 | u_)), (f in (m0 | u_))) for u_ in (m1g, m2g)]
    assert sorted(uses) == [(False, True), (True, False)]
    # h-values of the Hamiltonian unions are 0 (survivors).
    for u_ in (m1g, m2g):
        assert apply_w([x_ - y_ for x_, y_ in
                        zip(_vec(m0 | u_, m), base)]) == 0
    # kappa = w(2E - 3C*) = lambda = 1/2.
    tau_e = [2 - 3 * v for v in base]
    assert sum(tau_e) == 0
    kappa = apply_w(tau_e)
    assert kappa == Fraction(1, 2) == lam
    return {"d_G_minus_dim_L": 1, "lost": 1, "lambda": str(lam),
            "w_s": str(Fraction(-1, 2)), "kappa": str(kappa),
            "identity_10": "exact integer vector equality",
            "flip_summaries": flip_summaries,
            "criterion_5": "q=2, beta=tau, two components",
            "phases": phase_rows,
            "scope": "Cube rail-deletion step by fresh enumeration and "
                     "exact rational quotient algebra; general proofs "
                     "reviewed in prose"}


def fractional_exclusion_checks():
    """Prism fractional values exclude integral certificates; central
    recurrence and negative-iterate arithmetic."""
    for m in range(4, 64, 2):
        lam = Fraction(1, m - 2)
        assert 0 < lam < 1 and lam.denominator != 1
        for j in range(1, 7):
            assert lam / (1 + 2 * j * lam) == Fraction(1, m - 2 + 2 * j)
    hits = {}
    for p in range(1, 6):
        for q in range(1, 21):
            val, hit = None, False
            for j in range(0, 13):
                den = q - 2 * j * p
                if den == 0:
                    break
                val = Fraction(-p, den)
                if val == Fraction(-1, 2):
                    hit = j
                    break
            expect = (q % (2 * p) == 0)
            assert (hit is not False) == expect, (p, q)
            if expect:
                assert hit == q // (2 * p) - 1
            hits[(p, q)] = hit if hit is not False else None
    return {"prism_values": "1/(m-2) in (0,1), non-integral, m=4..62",
            "recurrence": "lambda_j = lambda/(1+2j*lambda), j=1..6",
            "negative_iterates": "-p/(q-2jp) reaches -1/2 iff 2p|q",
            "scope": "exact rational arithmetic"}


def block_cover_checks():
    """Coefficient-cover counting behind (7)/(8): the all-(k-1)-block
    family covers every index exactly once with weights 1/(k-1), and
    the summed identity Sigma theta_I (T_I - C) = F - C holds
    coordinatewise for arbitrary increment vectors."""
    for k in range(3, 9):
        blocks = [I for I in itertools.combinations(range(k), k - 1)]
        assert len(blocks) == k
        for i in range(k):
            total = sum(Fraction(1, k - 1) for I in blocks if i in I)
            assert total == 1
    k = 4
    blocks = [I for I in itertools.combinations(range(k), k - 1)]
    vecs = [[Fraction(3 * i + j - 2) for j in range(5)]
            for i in range(k)]
    lhs = [Fraction(0)] * 5
    for I in blocks:
        for i in I:
            lhs = [a + Fraction(1, k - 1) * b
                   for a, b in zip(lhs, vecs[i])]
    rhs = [Fraction(0)] * 5
    for v in vecs:
        rhs = [a + b for a, b in zip(rhs, v)]
    assert lhs == rhs
    return {"all_k_minus_1_cover": "exact for k=3..8",
            "summed_identity": "coordinatewise check, k=4",
            "scope": "exact rational arithmetic; the cover lemma's "
                     "domain discussion reviewed in prose"}


def formal_checks():
    return {
        "inherited_i193_formal_checks": PREVIOUS["formal_checks"](),
        "scope": "Flip criterion, fractional exclusion, matching "
                 "bookkeeping and block covers checked on exact "
                 "instances or by exact arithmetic; general proofs "
                 "reviewed in prose",
    }


def replay():
    before = authenticate()
    cube = cube_flip_checks()
    exclusion = fractional_exclusion_checks()
    covers = block_cover_checks()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "cube_flip_obstruction": cube,
            "fractional_exclusion": exclusion,
            "block_covers": covers,
            "formal_checks": checks,
            "sealed_reference_replay": reference,
            "I194_computational_seal": False,
            "local_ear_mechanism": "PARKED", "E183_line": "PARKED",
            "short_gap_front": "PARKED at J194 per the brief's "
                               "stopping rule",
            "universal_exchange": "UNRESOLVED at J192 (long-gap "
                                  "clauses)",
            "Q164": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i194-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I194 hashes, cube flip obstruction, fractional "
          "exclusion and inherited replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
