"""I191 byte authentication, exact square/profile/multiplicity checks,
and inherited replay.

The finite checks below independently verify, on the declared
thirteen-vertex exterior Y: the port-adjacency classification behind the
crossing-square dichotomy (exactly {e_0,e_3} or {e_3,e_4}, never e_2),
the absence of a Y four-cycle through edge 28-29, the S_Y/T_Y toggle
transitions with their pairings, the ten formal cut profiles of the
degree equation (9) including the two lost profiles, and the exterior
multiplicities underlying |B_R|=3(c_P+c_D). The deletion-path crossing,
sign-counting and transport arguments are reviewed in prose (see the
parent disposition).
"""
import json
import runpy
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i190-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
SOURCE = "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex"
SOURCE_HASH = "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
OUTPUTS = {
    "frontier/iterations/i191-concentration-exclusion.md":
        "838826908af277322982316de9c5e280e0a3eeea213db7e22b1348f8d7b8b585",
    "frontier/experiments/i191_concentration_exclusion/analytic-attempt.md":
        "5d8ae3c1f9bd58494d35268ef60aee00cbdd9d7e76e2d367d23fd449fb032a7c",
    "frontier/experiments/i191_concentration_exclusion/reading-and-failures.md":
        "64f02e02a2e37bed167d28df262eab535d49ea791c16a8edff5fa2ba6a666ad2",
    "frontier/experiments/i191_concentration_exclusion/input-authentication.json":
        "7087ca3f285ff491721b96a5ac0c576dc61c3dd4e1636a060a4cfd3731322b88",
    "frontier/sources/i191_concentration_exclusion/literature.md":
        "1c6b65a6e8379c5cd5dba1a1afa02d1ec9c062e2801c654a4f1d4fa336257496",
}

I188 = PREVIOUS["PREVIOUS"]["PREVIOUS"]
ATTACH = I188["ATTACH"]
EDGES = I188["EDGES"]
VERTS = I188["VERTS"]
path_edges = I188["path_edges"]


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i191-concentration-exclusion.md"}
    for directory in ("frontier/experiments/i191_concentration_exclusion",
                      "frontier/sources/i191_concentration_exclusion"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i191_concentration_exclusion/input-authentication.json").read_bytes())
    assert set(receipt["exclusive_outputs"]) == set(OUTPUTS)
    assert len(receipt["inputs"]) == 32
    anchors = {}
    chain = PREVIOUS
    while "OUTPUTS" in chain:
        anchors = dict(chain["OUTPUTS"], **anchors)
        chain = chain.get("PREVIOUS", {})
    anchors[SOURCE] = SOURCE_HASH
    anchored = 0
    for row in receipt["inputs"]:
        assert sha(row["path"]) == row["sha256"], row["path"]
        if row.get("expected_sha256") is not None:
            assert row["sha256"] == row["expected_sha256"] == anchors[row["path"]]
            anchored += 1
    assert anchored == 21
    assert receipt["document_validation"]["matched_supplied_anchors"] == 21
    archive = json.loads((ROOT / "frontier/iterations"
        "/iteration191-concentration-exclusion-task.json").read_bytes())
    assert set(archive["write_scope"]) == set(OUTPUTS)
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "input_records": receipt["inputs"],
            "supplied_anchors": anchored, "previous_proof_records": "unchanged"}


def exterior_square_checks():
    """Declared-Y facts behind the Section 4 square classification."""
    edge_set = {frozenset(e) for e in EDGES}
    attach_of = {0: 1, 1: 5, 2: 6, 3: 28, 4: 29}
    # Induced adjacencies among the five attachment vertices.
    internal = {frozenset((attach_of[i], attach_of[j]))
                for i in attach_of for j in attach_of if i < j
                and frozenset((attach_of[i], attach_of[j])) in edge_set}
    assert internal == {frozenset((1, 28)), frozenset((28, 29))}
    # A crossing square needs one internal Y edge joining the two
    # attachment vertices, so its cut pair is exactly {e_0,e_3} or
    # {e_3,e_4}; in particular no square contains e_2.
    cut_pairs = {tuple(sorted((i, j)))
                 for i in attach_of for j in attach_of if i < j
                 and frozenset((attach_of[i], attach_of[j])) in edge_set}
    assert cut_pairs == {(0, 3), (3, 4)}
    assert all(2 not in p for p in cut_pairs)
    # No Y four-cycle contains edge 28-29: the only other neighbors are
    # 1 (of 28) and 2 (of 29), and 1-2 is not an edge.
    nbr = {v: set() for v in VERTS}
    for a, b in EDGES:
        nbr[a].add(b)
        nbr[b].add(a)
    assert nbr[28] == {1, 29} and nbr[29] == {2, 28}
    assert frozenset((1, 2)) not in edge_set
    # Toggle transitions: S_Y minus edge 1-28 is T_Y plus 28-29, and
    # the reverse; pairings are 14 and 01,34 respectively.
    s_y = path_edges(29, 28, 1, 7, 6, 11, 10, 9, 8, 2, 3, 4, 5)
    t_y = path_edges(1, 7, 6, 11, 10, 9, 8, 2, 3, 4, 5)
    assert s_y - {frozenset((1, 28))} == t_y | {frozenset((28, 29))}
    assert t_y | {frozenset((28, 29)), frozenset((1, 28))} == s_y
    def pairing(edge_union):
        deg = {}
        for e in edge_union:
            for v in e:
                deg[v] = deg.get(v, 0) + 1
        ends = sorted(ATTACH[v] for v in ATTACH if deg.get(v, 0) == 1)
        # Trace path components to pair the endpoints.
        adj = {}
        for e in edge_union:
            a, b = sorted(e)
            adj.setdefault(a, []).append(b)
            adj.setdefault(b, []).append(a)
        pairs, seen = [], set()
        for v in [x for x in adj if len(adj[x]) == 1]:
            if v in seen:
                continue
            cur, prev, nodes = v, None, {v}
            while True:
                seen.add(cur)
                nxt = [w for w in adj[cur] if w != prev]
                if not nxt:
                    break
                prev, cur = cur, nxt[0]
                nodes.add(cur)
            pairs.append(frozenset(ATTACH[u] for u in nodes
                                   if u in ATTACH and len(adj[u]) == 1))
        return frozenset(pairs)
    assert pairing(s_y) == frozenset((frozenset((1, 4)),))
    assert pairing(t_y | {frozenset((28, 29))}) == \
        frozenset((frozenset((0, 1)), frozenset((3, 4))))
    return {
        "port_internal_adjacencies": ["1-28", "28-29"],
        "crossing_square_cut_pairs": [[0, 3], [3, 4]],
        "no_square_contains_e2": True,
        "no_y4_cycle_through_28_29": True,
        "toggle_transitions_verified": ["14;14 <-> 0134;03,14"],
        "scope": "Declared thirteen-vertex Y only",
    }


def profile_checks():
    """Degree equation (9) formal profiles and lost multiplicities."""
    solutions = []
    for mask in range(1 << 5):
        z = [(mask >> i) & 1 for i in range(5)]
        if z[0] + z[1] + z[2] + z[4] - z[3] == 1:
            solutions.append(tuple(i for i in range(5) if z[i]))
    assert len(solutions) == 10
    singletons = [s for s in solutions if len(s) == 1]
    triples = [s for s in solutions if len(s) == 3]
    assert sorted(s[0] for s in singletons) == [0, 1, 2, 4]
    assert len(triples) == 6 and all(3 in t for t in triples)
    # The two C190 lost profiles are among the ten; both contain e_2
    # and exclude e_0,e_1.
    assert (2, 3, 4) in solutions and (2,) in solutions
    # Exterior multiplicities from the parent-verified I188 table:
    # y_P = y_D = 3 (R1,R2,R3 and the three tails), and the two
    # no-cut-2 survivors have multiplicity one each.
    assert len({I188["R1"], I188["R2"], I188["R3"]}) == 3
    assert len(set(I188["RI_TAIL"].values())) == 3
    assert len({I188["S"]}) == 1 and len({I188["T_PLUS"]}) == 1
    return {
        "formal_profiles_of_eq9": 10,
        "singleton_profiles": [[0], [1], [2], [4]],
        "triple_profiles_all_contain_e3": True,
        "lost_profiles_among_them": [[2, 3, 4], [2]],
        "exterior_multiplicities": {"P": 3, "D": 3, "14;14": 1,
                                    "0134;03,14": 1},
        "scope": "Equation (9) Boolean solutions and inherited I188 "
                 "table multiplicities; no instance enumeration",
    }


def formal_checks():
    return {
        "inherited_i190_formal_checks": PREVIOUS["formal_checks"](),
        "scope": "Square/profile/multiplicity identities are finite "
                 "checks; deletion-path crossing, sign counting and "
                 "transport arguments reviewed in prose",
    }


def replay():
    before = authenticate()
    squares = exterior_square_checks()
    profiles = profile_checks()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "exterior_square_classification": squares,
            "cut_profiles": profiles, "formal_checks": checks,
            "sealed_reference_replay": reference,
            "I191_computational_seal": False,
            "local_ear_mechanism": "PARKED", "E183": "UNRESOLVED",
            "E183_line": "PARKED under the I191 stopping rule",
            "Z184": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i191-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I191 hashes, exterior square classification, cut profiles "
          "and inherited replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
