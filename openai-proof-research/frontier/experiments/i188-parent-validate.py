"""I188 byte authentication, exact exterior enumeration, and inherited replay.

The finite check below is an exhaustive binary solution of the thirteen
declared exterior degree equations on the fixed thirteen-vertex graph Y,
together with path/pairing and gluing identities. It independently
verifies the I188 analytic Section 6.2 classification table. Faciality,
dual distinctness, sign consistency, nonvanishing and white-tree leaf
arguments are reviewed in prose (see the parent disposition).
"""
import itertools
import json
import runpy
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i187-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
SOURCE = "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex"
SOURCE_HASH = "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
OUTPUTS = {
    "frontier/iterations/i188-patch-rooted-state.md":
        "3489a0d5a98d7f48f34e05853eb875651d7d7b9b2e96a05667a0beedbbab8e29",
    "frontier/experiments/i188_patch_rooted_state/analytic-attempt.md":
        "d1fc472d25e74f345bb0ed79d7df1aa8074ef0f0278f5f5f826f69816707de5c",
    "frontier/experiments/i188_patch_rooted_state/reading-and-failures.md":
        "f7bca5bf8df8eaa93a13c09ea34593fadcc724e1ee108848a8c65cdc3228f3ff",
    "frontier/experiments/i188_patch_rooted_state/input-authentication.json":
        "4825a58ef9794675587b8a9012452f550409a2de750304b408091fb174669a47",
    "frontier/sources/i188_patch_rooted_state/literature.md":
        "937b693acbde539b774ad203981065d46d3ad4abfb1efce7120fdbb4af5ef8c9",
}

VERTS = (1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 28, 29)
EDGES = ((1, 7), (1, 28), (2, 3), (2, 8), (2, 29), (3, 4), (3, 9),
         (4, 5), (4, 10), (5, 11), (6, 7), (6, 11), (7, 8), (8, 9),
         (9, 10), (10, 11), (28, 29))
ATTACH = {1: 0, 5: 1, 6: 2, 28: 3, 29: 4}
INTERIOR = tuple(v for v in VERTS if v not in ATTACH)


def path_edges(*vertices):
    return frozenset(frozenset((a, b)) for a, b in zip(vertices, vertices[1:]))


R1 = path_edges(1, 28, 29, 2, 3, 4, 10, 9, 8, 7, 6, 11, 5)
R2 = path_edges(1, 28, 29, 2, 3, 9, 8, 7, 6, 11, 10, 4, 5)
R3 = path_edges(1, 28, 29, 2, 8, 7, 6, 11, 10, 9, 3, 4, 5)
S = path_edges(29, 28, 1, 7, 6, 11, 10, 9, 8, 2, 3, 4, 5)
T_PLUS = path_edges(1, 7, 6, 11, 10, 9, 8, 2, 3, 4, 5) | {frozenset((28, 29))}
RI_TAIL = {r: frozenset(e for e in r if 1 not in e and 28 not in e)
           | {frozenset((1, 28))} for r in (R1, R2, R3)}


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i188-patch-rooted-state.md"}
    for directory in ("frontier/experiments/i188_patch_rooted_state",
                      "frontier/sources/i188_patch_rooted_state"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i188_patch_rooted_state/input-authentication.json").read_bytes())
    assert set(receipt["exclusive_outputs"]) == set(OUTPUTS)
    assert len(receipt["inputs"]) == 17
    anchors = dict(PREVIOUS["OUTPUTS"], **{SOURCE: SOURCE_HASH})
    anchored = 0
    for row in receipt["inputs"]:
        assert sha(row["path"]) == row["sha256"], row["path"]
        if row.get("expected_sha256") is not None:
            assert row["sha256"] == row["expected_sha256"] == anchors[row["path"]]
            anchored += 1
    assert anchored == 6
    archive = json.loads((ROOT / "frontier/iterations"
        "/iteration188-patch-rooted-state-codex-astra-resume2-task.json").read_bytes())
    assert set(archive["write_scope"]) == set(OUTPUTS)
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "input_records": receipt["inputs"],
            "supplied_anchors": anchored, "previous_proof_records": "unchanged"}


def exterior_checks():
    """Exhaustively solve the I188 Section 6.2 binary degree equations."""
    assert len(EDGES) == 17 and len(VERTS) == 13 and len(INTERIOR) == 8
    assert len({frozenset(e) for e in EDGES}) == 17
    incidence = {v: [] for v in VERTS}
    for i, (a, b) in enumerate(EDGES):
        assert a in incidence and b in incidence and a != b
        incidence[a].append(i)
        incidence[b].append(i)
    assert {v: len(incidence[v]) for v in ATTACH} == {1: 2, 5: 2, 6: 2, 28: 2, 29: 2}
    assert all(len(incidence[v]) == 3 for v in INTERIOR)
    # Y is connected and bipartite, with attachments split 4/1 by color;
    # degree summation then yields equation (15) for every packing.
    color = {1: 0}
    queue = [1]
    while queue:
        v = queue.pop()
        for i in incidence[v]:
            w = EDGES[i][0] if EDGES[i][1] == v else EDGES[i][1]
            if w not in color:
                color[w] = 1 - color[v]
                queue.append(w)
            else:
                assert color[w] != color[v]
    assert len(color) == 13
    assert sorted(ATTACH[v] for v in color if v in ATTACH and not color[v]) == \
        [0, 1, 2, 4]
    assert [ATTACH[v] for v in color if v in ATTACH and color[v]] == [3]
    packings = {}
    for mask in range(1 << 17):
        degree = dict.fromkeys(VERTS, 0)
        for i in range(17):
            if (mask >> i) & 1:
                degree[EDGES[i][0]] += 1
                degree[EDGES[i][1]] += 1
        if any(degree[v] != 2 for v in INTERIOR):
            continue
        if any(degree[v] not in (1, 2) for v in ATTACH):
            continue
        used = tuple(sorted(p for v, p in ATTACH.items() if degree[v] == 1))
        adjacency = {v: [] for v in VERTS}
        for i in range(17):
            if (mask >> i) & 1:
                adjacency[EDGES[i][0]].append(EDGES[i][1])
                adjacency[EDGES[i][1]].append(EDGES[i][0])
        seen, paths, cyclic = set(), [], False
        for start in VERTS:
            if start in seen:
                continue
            component, stack = set(), [start]
            while stack:
                v = stack.pop()
                if v in component:
                    continue
                component.add(v)
                stack.extend(adjacency[v])
            seen |= component
            if all(degree[v] == 2 for v in component):
                cyclic = True
                break
            endpoints = sorted(ATTACH[v] for v in component
                               if v in ATTACH and degree[v] == 1)
            assert len(endpoints) == 2
            paths.append(frozenset(endpoints))
        if cyclic:
            continue
        edge_set = frozenset(frozenset(EDGES[i]) for i in range(17)
                             if (mask >> i) & 1)
        packings.setdefault(used, []).append((frozenset(paths), edge_set))
    eq15 = lambda u: len(set(u) & {0, 1, 2, 4}) - (3 in u) == 2
    no2 = {u: v for u, v in packings.items() if 2 not in u and eq15(u)}
    # U=01: exactly R1, R2, R3, pairing 01.
    assert {e for _, e in no2.pop((0, 1))} == {R1, R2, R3}
    # U=04: no admissible packing at all.
    assert (0, 4) not in packings
    # U=14: exactly S, pairing 14.
    assert {e for _, e in no2.pop((1, 4))} == {S}
    # U=0134: exactly three packings with pairing 03,14 and one with 01,34.
    four = no2.pop((0, 1, 3, 4))
    p0314 = frozenset((frozenset((0, 3)), frozenset((1, 4))))
    p0134 = frozenset((frozenset((0, 1)), frozenset((3, 4))))
    assert {e for p, e in four if p == p0314} == set(RI_TAIL.values())
    assert {e for p, e in four if p == p0134} == {T_PLUS}
    assert len(four) == 4
    # The (15)-admissible no-2 used sets are exactly the four classified.
    assert not no2
    # Every realizable used set satisfies the color-balance equation (15).
    assert all(eq15(u) for u in packings)
    with2 = {u: len(v) for u, v in packings.items() if 2 in u}
    assert set(with2) == {(0, 2), (1, 2), (2, 4), (0, 1, 2, 3),
                          (0, 2, 3, 4), (1, 2, 3, 4)}
    # Gluing lemma on four used ports: distinct pairings give one cycle.
    ports4 = (0, 1, 3, 4)
    matchings = [frozenset((frozenset((a, b)), frozenset((c, d))))
                 for a, b, c, d in itertools.permutations(ports4)
                 if a < b and c < d and a < c]
    assert len(matchings) == 3
    for first, second in itertools.product(matchings, repeat=2):
        edges = [tuple(sorted(e)) for e in first | second]
        if first == second:
            # Two doubled edges: the glued union splits into two cycles.
            assert len(edges) == 2
        else:
            # Distinct pairings: one 2-regular connected graph, one cycle.
            assert len(edges) == 4
            adjacency = {p: [] for p in ports4}
            for a, b in edges:
                adjacency[a].append(b)
                adjacency[b].append(a)
            assert all(len(adjacency[p]) == 2 for p in ports4)
            seen, stack = set(), [ports4[0]]
            while stack:
                v = stack.pop()
                if v not in seen:
                    seen.add(v)
                    stack.extend(adjacency[v])
            assert seen == set(ports4)
    return {
        "binary_assignments_tested": 1 << 17,
        "valid_exterior_packings": sum(map(len, packings.values())),
        "used_sets_realizable": {",".join(map(str, u)): len(v)
                                 for u, v in sorted(packings.items())},
        "no2_classification": {
            "01": {"packings": 3, "pairing": "01", "named": ["R1", "R2", "R3"]},
            "04": {"packings": 0},
            "14": {"packings": 1, "pairing": "14", "named": ["S"]},
            "0134": {"pairing 03,14": 3, "pairing 01,34": 1,
                     "named": ["R1|R2|R3 tails + (1-28)", "T + (28-29)"]},
        },
        "all_realizable_used_sets_satisfy_eq15": True,
        "y_bipartition_attachments": {"color0_ports": [0, 1, 2, 4],
                                      "color1_ports": [3]},
        "with2_used_sets": [list(u) for u in sorted(with2)],
        "gluing_distinct_pairings_single_cycle": True,
        "scope": "Exact exterior enumeration on the declared 13-vertex graph; "
                 "no patch/dual/state objects enumerated",
    }


def formal_checks():
    # One fixed sign specialization of the reviewed I187 (14): the phase
    # (-i)^{c(D)} eps_* must equal (-i)^{q+f_+} i^{f_-} with q = c(D)-1,
    # f_+ = 1 iff eps_* = +1, f_- = 1 - f_+, as powers of i modulo 4.
    for c in range(1, 9):
        for eps in (1, -1):
            f_plus = 1 if eps == 1 else 0
            f_minus = 1 - f_plus
            assert (3 * c + (0 if eps == 1 else 2)) % 4 == \
                (3 * (c - 1 + f_plus) + f_minus) % 4
    # Exactly 2^(c-1) of the 2^c orientations pass the one-fixed-sign mark.
    for c in range(1, 9):
        assert sum(1 for signs in itertools.product((-1, 1), repeat=c)
                   if signs[0] == 1) == 2 ** (c - 1)
    return {
        "one_fixed_sign_phase_cases": 16,
        "retained_orientation_counts": 8,
        "inherited_i187_formal_checks": PREVIOUS["formal_checks"](),
        "scope": "Phase and orientation-count algebra only; the restricted "
                 "Taylor coefficient itself is reviewed in prose",
    }


def replay():
    before = authenticate()
    exterior = exterior_checks()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "exterior_enumeration": exterior, "formal_checks": checks,
            "sealed_reference_replay": reference,
            "I188_computational_seal": False,
            "local_ear_mechanism": "PARKED", "E183": "UNRESOLVED",
            "Z184": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i188-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I188 hashes, exact exterior enumeration, formal checks and "
          "inherited replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
