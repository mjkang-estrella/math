"""I190 byte authentication, exact patch-matching enumeration, structural
identity checks, and inherited replay.

The finite checks below independently re-derive the I190 Section 1.3
patch matching/deletion table by enumerating all 2^11 subsets of the
eleven declared local edges and selecting perfect matchings of the
ten-vertex local graph, grouped by the continuation set J; verify the
alpha/beta component-count identity and the lost-type cut-profile
mapping (8); and cross-check the inherited Section 4.1 exterior
witnesses against the parent-verified I189 witness data. Connectivity,
tight-shore, Pfaffian-sign and square-switch arguments are reviewed in
prose (see the parent disposition).
"""
import json
import runpy
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i189-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
SOURCE = "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex"
SOURCE_HASH = "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
OUTPUTS = {
    "frontier/iterations/i190-beta-pairing-survivor.md":
        "fc6808265d95a743e755c58bb1382e18b3d937d9807cdd3c4ef877d2fb8168fe",
    "frontier/experiments/i190_beta_pairing_survivor/analytic-attempt.md":
        "e08d62b11e38ccd65561a0084b1e35135e3cc76608512da10ed2b47bc664539a",
    "frontier/experiments/i190_beta_pairing_survivor/reading-and-failures.md":
        "652f115871c6a013c169072cef7bb84fc4b49dad138d99ad2aef2e244fa62994",
    "frontier/experiments/i190_beta_pairing_survivor/input-authentication.json":
        "083272b4f4547f9d31b0f932e0d4baeee70c2661bad50f50df2d79e909c26890",
    "frontier/sources/i190_beta_pairing_survivor/literature.md":
        "dc79cc3e4a0b45524dd514f7a3aa97d6455d3962114aa1b72c9aad487c20d2a1",
}

LOCAL = PREVIOUS["LOCAL"]
CONT_INDEX = {"a": 7, "b": 8, "c": 9, "d": 10}

# Claimed Section 1.3 table: J -> set of matchings, each a frozenset of
# indices into LOCAL. Terminals in J are matched by their continuation.
J_TABLE = {
    frozenset(): {frozenset((0, 2, 4)), frozenset((1, 3, 5)),
                  frozenset((1, 4, 6))},
    frozenset("ab"): {frozenset((4, 6)), frozenset((3, 5))},
    frozenset("cd"): {frozenset((1, 6)), frozenset((0, 2))},
    frozenset("ad"): {frozenset((2, 5))},
    frozenset("bc"): {frozenset((0, 3))},
    frozenset("abcd"): {frozenset((6,))},
}

# Section 4.1 inherited four-port witnesses, in the same order as the
# I189 parent's WITNESSES rows 1..6.
W6 = (
    ((1, 7, 6), (5, 11, 10, 4, 3, 9, 8, 2, 29, 28)),
    ((1, 7, 8, 9, 10, 4, 3, 2, 29, 28), (5, 11, 6)),
    ((1, 7, 8, 2, 3, 9, 10, 4, 5, 11, 6), (28, 29)),
    ((1, 28), (6, 7, 8, 9, 10, 11, 5, 4, 3, 2, 29)),
    ((5, 11, 6), (28, 1, 7, 8, 9, 10, 4, 3, 2, 29)),
    ((5, 11, 10, 4, 3, 9, 8, 2, 29), (6, 7, 1, 28)),
)


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i190-beta-pairing-survivor.md"}
    for directory in ("frontier/experiments/i190_beta_pairing_survivor",
                      "frontier/sources/i190_beta_pairing_survivor"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i190_beta_pairing_survivor/input-authentication.json").read_bytes())
    assert set(receipt["exclusive_outputs"]) == set(OUTPUTS)
    assert len(receipt["inputs"]) == 26
    anchors = dict(PREVIOUS["OUTPUTS"])
    anchors.update(PREVIOUS["PREVIOUS"]["OUTPUTS"])
    anchors.update(PREVIOUS["PREVIOUS"]["PREVIOUS"]["OUTPUTS"])
    anchors[SOURCE] = SOURCE_HASH
    anchored = 0
    for row in receipt["inputs"]:
        assert sha(row["path"]) == row["sha256"], row["path"]
        if row.get("expected_sha256") is not None:
            assert row["sha256"] == row["expected_sha256"] == anchors[row["path"]]
            anchored += 1
    assert anchored == 16
    assert receipt["document_validation"]["matched_prior_output_anchors"] == 15
    assert receipt["document_validation"]["matched_manuscript_anchor"] is True
    archive = json.loads((ROOT / "frontier/iterations"
        "/iteration190-beta-pairing-survivor-task.json").read_bytes())
    assert set(archive["write_scope"]) == set(OUTPUTS)
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "input_records": receipt["inputs"],
            "supplied_anchors": anchored, "previous_proof_records": "unchanged"}


def patch_matching_checks():
    """Exhaustively re-derive the Section 1.3 J-grouped matching table."""
    assert len(LOCAL) == 11
    vertices = ["x", "a", "b", "y", "d", "c"]
    terminals = ["a'", "b'", "c'", "d'"]
    found = {}
    for mask in range(1 << 11):
        chosen = [i for i in range(11) if (mask >> i) & 1]
        covered = {}
        for i in chosen:
            for v in LOCAL[i]:
                covered[v] = covered.get(v, 0) + 1
        # Patch vertices matched exactly once; a terminal is matched
        # iff its continuation is used (it has no other incident edge).
        if any(covered.get(v, 0) != 1 for v in vertices):
            continue
        if any(covered.get(v, 0) > 1 for v in terminals):
            continue
        jset = frozenset(k for k, idx in CONT_INDEX.items() if idx in chosen)
        internal = frozenset(i for i in chosen if i < 7)
        found.setdefault(jset, set()).add(internal)
    assert set(found) == set(J_TABLE), sorted(map(sorted, found))
    for jset, matchings in J_TABLE.items():
        assert found[jset] == matchings, jset
    total = sum(map(len, found.values()))
    assert total == 10
    # J=ac and J=bd are exactly the same-color pairs and have none.
    assert frozenset("ac") not in found and frozenset("bd") not in found
    # Consistency with the I189 Hamiltonian rows: every complementary
    # local matching of a Hamiltonian candidate appears in this table.
    all_matchings = set().union(*J_TABLE.values())
    for name, matching in PREVIOUS["MATCHINGS"].items():
        internal = frozenset(i for i in matching if i < 7)
        assert internal in all_matchings, name
    return {
        "binary_assignments_tested": 1 << 11,
        "perfect_matchings_total": total,
        "j_groups": {"".join(sorted(j)) or "empty": len(m)
                     for j, m in sorted(J_TABLE.items(),
                                        key=lambda kv: (len(kv[0]), sorted(kv[0])))},
        "same_color_pairs_impossible": ["ac", "bd"],
        "consistent_with_i189_complements": True,
        "scope": "Exact perfect-matching enumeration on the declared "
                 "eleven-edge local graph; no global instances enumerated",
    }


def identity_checks():
    """Component-count identity (1) and lost-type cut profiles (8)."""
    # On four labels, two pairings glue to one cycle iff distinct.
    labels = ("a", "b", "c", "d")
    alpha = frozenset((frozenset("ab"), frozenset("cd")))
    beta = frozenset((frozenset("ac"), frozenset("bd")))
    for first, second, expected in ((alpha, alpha, 2), (beta, beta, 2),
                                    (alpha, beta, 1)):
        adjacency = {v: [] for v in labels}
        for e in first | second:
            a, b = sorted(e)
            adjacency[a].append(b)
            adjacency[b].append(a)
        seen, count = set(), 0
        for v in labels:
            if v in seen:
                continue
            count += 1
            stack = [v]
            while stack:
                u = stack.pop()
                if u not in seen:
                    seen.add(u)
                    stack.extend(adjacency[u])
        assert count == expected
    # Canonical cut profile: at each port, exactly one of e_i and the
    # matching alternative; N uses e_i iff i is NOT in U. The lost
    # fibres give N intersect {e_0..e_4} = {e_2,e_3,e_4} for P and
    # {e_2} for D, exactly as (8) states.
    ports = {0, 1, 2, 3, 4}
    lost = {"P": frozenset((0, 1)), "D": frozenset((0, 1, 3, 4))}
    profiles = {k: frozenset(ports - set(u)) for k, u in lost.items()}
    assert profiles["P"] == frozenset((2, 3, 4))
    assert profiles["D"] == frozenset((2,))
    # Both profiles contain e_2 and avoid e_0,e_1, as (8) concludes.
    assert all(2 in p and not ({0, 1} & p) for p in profiles.values())
    # The six inherited Section 4.1 witnesses match the parent-verified
    # I189 witness edge sets exactly.
    path_edges = PREVIOUS["path_edges"]
    expected = [tuple(path_edges(*p) for p in paths)
                for _, _, paths in PREVIOUS["WITNESSES"][:6]]
    actual = [tuple(path_edges(*p) for p in paths) for paths in W6]
    assert actual == expected
    return {
        "component_count_identity_cases": 3,
        "lost_cut_profiles": {"P": sorted(profiles["P"]),
                              "D": sorted(profiles["D"])},
        "inherited_witnesses_match_i189": 6,
        "scope": "Four-label gluing and cut-membership bookkeeping; "
                 "parity, crossing and sign arguments reviewed in prose",
    }


def formal_checks():
    return {
        "inherited_i189_formal_checks": PREVIOUS["formal_checks"](),
        "scope": "Matching-table enumeration and gluing/profile "
                 "identities are finite checks; connectivity, tight "
                 "shore, Pfaffian sign and square switch reviewed in prose",
    }


def replay():
    before = authenticate()
    matchings = patch_matching_checks()
    identities = identity_checks()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "patch_matching_table": matchings,
            "structural_identities": identities, "formal_checks": checks,
            "sealed_reference_replay": reference,
            "I190_computational_seal": False,
            "local_ear_mechanism": "PARKED", "E183": "UNRESOLVED",
            "Z184": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i190-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I190 hashes, exact patch-matching enumeration, structural "
          "identities and inherited replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
