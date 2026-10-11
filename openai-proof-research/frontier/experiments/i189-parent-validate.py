"""I189 byte authentication, exhaustive patch-restriction classification,
exterior witness checks, and inherited replay.

The finite check below independently re-derives the I189 Section 1
ten-row classification by enumerating all 2^11 subsets of the eleven
declared local edges and imposing degree two at the six patch vertices,
and verifies every displayed exterior witness path of Section 3.3 against
the declared thirteen-vertex graph Y. Pairing/planarity, matching-repair
and transport arguments are reviewed in prose (see the parent
disposition).
"""
import itertools
import json
import runpy
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT / "frontier/experiments"
PREVIOUS = runpy.run_path(str(EXP / "i188-parent-validate.py"))
REFERENCE = PREVIOUS["REFERENCE"]
sha = PREVIOUS["sha"]
SOURCE = "frontier/sources/i164_structural_graph_discovery/upstream-paper.tex"
SOURCE_HASH = "03f59643501a21f2b20c138ff10769fde41523008845b2528bf646b4a769dd56"
OUTPUTS = {
    "frontier/iterations/i189-patch-route-transport.md":
        "aa2f6bf9895a13616e50ed4e00e58ab67cbb1c419305ac47a3f8980f288aa3bc",
    "frontier/experiments/i189_patch_route_transport/analytic-attempt.md":
        "933cc7de3160960a707042bceae32d4994540dfea008b2a52b1e4f73a8e1eee0",
    "frontier/experiments/i189_patch_route_transport/reading-and-failures.md":
        "a5e2270acce653fd48ca27e1768e3a8656a9c023c1d5174071383ccdcbdb1eb5",
    "frontier/experiments/i189_patch_route_transport/input-authentication.json":
        "af8f841f730e6913ea34ac5a9d41c68424353b94ab360690a15abe6e5f88c1d6",
    "frontier/sources/i189_patch_route_transport/literature.md":
        "d4977bb0d1b1e5ad7200587a3341fb6b3d7b6047766fcaa7bfb64e6b734e583f",
}

# The eleven declared local edges: the hexagon, the chord, and the four
# continuations. Terminals are dangling ends labelled by letter.
PATCH = ("x", "a", "b", "y", "d", "c")
LOCAL = (("x", "a"), ("a", "b"), ("b", "y"), ("y", "d"), ("d", "c"),
         ("c", "x"), ("x", "y"), ("a", "a'"), ("b", "b'"), ("c", "c'"),
         ("d", "d'"))
CONT = {"a": ("a", "a'"), "b": ("b", "b'"), "c": ("c", "c'"),
        "d": ("d", "d'")}

# The ten claimed rows: (name, internal edge letters among the first
# seven of LOCAL, used continuation letters, has closed cycle component).
ROWS = (
    ("Z", frozenset((0, 1, 2, 3, 4, 5)), frozenset(), True),
    ("L_ab", frozenset((0, 2, 3, 4, 5)), frozenset("ab"), False),
    ("L_cd", frozenset((0, 1, 2, 3, 5)), frozenset("cd"), False),
    ("F", frozenset((0, 2, 3, 5)), frozenset("abcd"), False),
    ("K_B", frozenset((0, 2, 4, 6)), frozenset("abcd"), False),
    ("Z_top", frozenset((0, 1, 2, 4, 6)), frozenset("cd"), True),
    ("K_A", frozenset((1, 3, 5, 6)), frozenset("abcd"), False),
    ("Z_bottom", frozenset((1, 3, 4, 5, 6)), frozenset("ab"), True),
    ("L_bc", frozenset((0, 1, 3, 4, 6)), frozenset("bc"), False),
    ("L_ad", frozenset((1, 2, 4, 5, 6)), frozenset("ad"), False),
)
# Claimed terminal pairings (frozenset of terminal pairs, empty for Z).
PAIRINGS = {
    "Z": frozenset(),
    "L_ab": frozenset((frozenset("ab"),)),
    "L_cd": frozenset((frozenset("cd"),)),
    "F": frozenset((frozenset("ac"), frozenset("bd"))),
    "K_B": frozenset((frozenset("ab"), frozenset("cd"))),
    "Z_top": frozenset((frozenset("cd"),)),
    "K_A": frozenset((frozenset("ab"), frozenset("cd"))),
    "Z_bottom": frozenset((frozenset("ab"),)),
    "L_bc": frozenset((frozenset("bc"),)),
    "L_ad": frozenset((frozenset("ad"),)),
}
# Claimed complementary local matching edges (indices into LOCAL).
MATCHINGS = {
    "K_A": frozenset((0, 2, 4)), "K_B": frozenset((1, 3, 5)),
    "F": frozenset((1, 4, 6)), "L_ab": frozenset((1, 6, 9, 10)),
    "L_cd": frozenset((4, 6, 7, 8)), "L_bc": frozenset((2, 5, 7, 10)),
    "L_ad": frozenset((0, 3, 8, 9)),
}

ATTACH = PREVIOUS["ATTACH"]
EDGES = PREVIOUS["EDGES"]
VERTS = PREVIOUS["VERTS"]
path_edges = PREVIOUS["path_edges"]

# Section 3.3 witnesses: (used port set, claimed exterior pairing,
# two paths as vertex sequences).
WITNESSES = (
    ((0, 1, 2, 3), ((0, 2), (1, 3)),
     ((1, 7, 6), (5, 11, 10, 4, 3, 9, 8, 2, 29, 28))),
    ((0, 1, 2, 3), ((0, 3), (1, 2)),
     ((1, 7, 8, 9, 10, 4, 3, 2, 29, 28), (5, 11, 6))),
    ((0, 2, 3, 4), ((0, 2), (3, 4)),
     ((1, 7, 8, 2, 3, 9, 10, 4, 5, 11, 6), (28, 29))),
    ((0, 2, 3, 4), ((0, 3), (2, 4)),
     ((1, 28), (6, 7, 8, 9, 10, 11, 5, 4, 3, 2, 29))),
    ((1, 2, 3, 4), ((1, 2), (3, 4)),
     ((5, 11, 6), (28, 1, 7, 8, 9, 10, 4, 3, 2, 29))),
    ((1, 2, 3, 4), ((1, 4), (2, 3)),
     ((5, 11, 10, 4, 3, 9, 8, 2, 29), (6, 7, 1, 28))),
    ((0, 1, 3, 4), ((0, 1), (3, 4)),
     ((1, 7, 6, 11, 10, 9, 8, 2, 3, 4, 5), (28, 29))),
    ((0, 1, 3, 4), ((0, 3), (1, 4)),
     ((1, 28), (5, 11, 6, 7, 8, 9, 10, 4, 3, 2, 29))),
)


def authenticate():
    for name, digest in OUTPUTS.items():
        assert sha(name) == digest, name
    found = {"frontier/iterations/i189-patch-route-transport.md"}
    for directory in ("frontier/experiments/i189_patch_route_transport",
                      "frontier/sources/i189_patch_route_transport"):
        for p in (ROOT / directory).rglob("*"):
            assert not p.is_symlink()
            if p.is_file():
                found.add(p.relative_to(ROOT).as_posix())
    assert found == set(OUTPUTS)
    receipt = json.loads((ROOT /
        "frontier/experiments/i189_patch_route_transport/input-authentication.json").read_bytes())
    assert set(receipt["exclusive_outputs"]) == set(OUTPUTS)
    assert len(receipt["inputs"]) == 20
    anchors = dict(PREVIOUS["OUTPUTS"])
    anchors.update(PREVIOUS["PREVIOUS"]["OUTPUTS"])
    anchors[SOURCE] = SOURCE_HASH
    anchored = 0
    for row in receipt["inputs"]:
        assert sha(row["path"]) == row["sha256"], row["path"]
        if row.get("expected_sha256") is not None:
            assert row["sha256"] == row["expected_sha256"] == anchors[row["path"]]
            anchored += 1
    assert anchored == 11
    assert receipt["document_validation"]["matched_I187_I188_anchors"] == 10
    assert receipt["document_validation"]["matched_manuscript_anchor"] is True
    archive = json.loads((ROOT / "frontier/iterations"
        "/iteration189-patch-route-transport-task.json").read_bytes())
    assert set(archive["write_scope"]) == set(OUTPUTS)
    PREVIOUS["authenticate"]()
    return {"output_hashes": OUTPUTS, "input_records": receipt["inputs"],
            "supplied_anchors": anchored, "previous_proof_records": "unchanged"}


def components(edge_indices):
    """Components of a restriction as (vertices-on-path-or-cycle) tuples.

    Terminals are treated as distinct dangling endpoints a',b',c',d'.
    Returns (paths, cycles): paths as endpoint terminal pairs, cycles as
    vertex sets.
    """
    adjacency = {}
    for i in edge_indices:
        a, b = LOCAL[i]
        adjacency.setdefault(a, []).append(b)
        adjacency.setdefault(b, []).append(a)
    seen = set()
    paths, cycles = [], []
    for start in adjacency:
        if start in seen:
            continue
        comp, stack = set(), [start]
        while stack:
            v = stack.pop()
            if v in comp:
                continue
            comp.add(v)
            seen.add(v)
            stack.extend(w for w in adjacency[v] if w not in comp)
        degrees = {v: len(adjacency[v]) for v in comp}
        if all(d == 2 for d in degrees.values()):
            cycles.append(frozenset(comp))
        else:
            ends = sorted(v.rstrip("'") for v in comp if degrees[v] == 1)
            assert len(ends) == 2
            paths.append(frozenset(ends))
    return frozenset(paths), frozenset(cycles)


def patch_checks():
    """Exhaustively re-derive the ten-row degree-two classification."""
    assert len(LOCAL) == 11 and len({frozenset(e) for e in LOCAL}) == 11
    incidence = {v: [] for v in PATCH}
    for i, (a, b) in enumerate(LOCAL):
        if a in incidence:
            incidence[a].append(i)
        if b in incidence:
            incidence[b].append(i)
    assert sorted(map(len, incidence.values())) == [3] * 6
    feasible = {}
    for mask in range(1 << 11):
        chosen = frozenset(i for i in range(11) if (mask >> i) & 1)
        if any(sum(i in chosen for i in incidence[v]) != 2 for v in PATCH):
            continue
        internal = frozenset(i for i in chosen if i < 7)
        letters = frozenset(k for k in CONT
                            if LOCAL.index(CONT[k]) in chosen)
        feasible[(internal, letters)] = chosen
    assert len(feasible) == 10
    expected = {(r[1], r[2]): r for r in ROWS}
    assert set(feasible) == set(expected)
    for key, chosen in feasible.items():
        name, _, _, has_cycle = expected[key]
        paths, cycles = components(chosen)
        assert bool(cycles) == has_cycle, name
        assert paths == PAIRINGS[name], (name, paths)
        if not has_cycle:
            # Complementary local edges meet every patch vertex exactly
            # once and a terminal exactly when its continuation is unused.
            matching = frozenset(set(range(11)) - chosen)
            assert matching == MATCHINGS[name], name
    # The three closed-cycle rows are the only excluded ones.
    assert [r[0] for r in ROWS if r[3]] == ["Z", "Z_top", "Z_bottom"]
    # Terminal colors: a',c' black; b',d' white. Alpha pairs opposite
    # colors; beta pairs same colors; the balanced two-letter sets are
    # exactly ab, ad, bc, cd, and every L row uses one of them.
    color = {"a": 0, "c": 0, "b": 1, "d": 1}
    alpha = PAIRINGS["K_A"]
    beta = PAIRINGS["F"]
    assert all(color[a] != color[b] for a, b in alpha)
    assert all(color[a] == color[b] for a, b in beta)
    balanced = {frozenset((u, v)) for u, v in itertools.combinations("abcd", 2)
                if color[u] != color[v]}
    assert balanced == {frozenset("ab"), frozenset("ad"), frozenset("bc"),
                        frozenset("cd")}
    for name in ("L_ab", "L_cd", "L_bc", "L_ad"):
        (pairing,) = PAIRINGS[name]
        assert pairing in balanced
    return {
        "binary_assignments_tested": 1 << 11,
        "degree_feasible_restrictions": 10,
        "closed_cycle_rows": ["Z", "Z_top", "Z_bottom"],
        "hamiltonian_candidates": ["L_ab", "L_cd", "F", "K_B", "K_A",
                                   "L_bc", "L_ad"],
        "all_row_structures_pairings_and_matchings_verified": True,
        "terminal_color_constraints_verified": True,
        "scope": "Exhaustive degree-two classification on the declared "
                 "eleven-edge local patch; no global instances enumerated",
    }


def witness_checks():
    """Verify every displayed Section 3.3 exterior path in writing."""
    edge_set = {frozenset(e) for e in EDGES}
    for used, pairing, paths in WITNESSES:
        occupied = []
        endpoints = []
        for path in paths:
            for a, b in zip(path, path[1:]):
                assert frozenset((a, b)) in edge_set, (used, path)
            assert len(set(path)) == len(path)
            occupied.extend(path)
            endpoints.append(frozenset(ATTACH[v] for v in (path[0], path[-1])))
        assert sorted(occupied) == sorted(VERTS)
        assert frozenset(endpoints) == frozenset(frozenset(p) for p in pairing)
        assert sorted(ATTACH[v] for v in ATTACH if v in occupied
                      and v in (paths[0][0], paths[0][-1],
                                paths[1][0], paths[1][-1])) == sorted(used)
    # Cross-check against the parent-verified I188 named packings: the
    # U=0134 row 7 first path is exactly T_Y, and the eight rows realize
    # eight distinct exterior pairings (six cut-2, two no-cut-2).
    assert path_edges(*WITNESSES[6][2][0]) == PREVIOUS["path_edges"](
        1, 7, 6, 11, 10, 9, 8, 2, 3, 4, 5)
    pairings = {frozenset(frozenset(e) for e in p) for _, p, _ in WITNESSES}
    assert len(pairings) == 8
    return {
        "witness_rows_verified": 8,
        "distinct_exterior_pairings": 8,
        "paths_vertex_disjoint_and_spanning": True,
        "all_edges_declared": True,
        "u0134_first_row_matches_i188_T": True,
        "scope": "Declared thirteen-vertex Y only; written witnesses, "
                 "no completeness claim beyond the I188 enumeration",
    }


def formal_checks():
    return {
        "inherited_i188_formal_checks": PREVIOUS["formal_checks"](),
        "scope": "Classification enumeration and witness verification are "
                 "finite checks; pairing/planarity, matching repair and "
                 "transport arguments are reviewed in prose",
    }


def replay():
    before = authenticate()
    patch = patch_checks()
    witnesses = witness_checks()
    checks = formal_checks()
    reference, proc = REFERENCE["replay"]()
    assert reference["status"] == "PASS" and authenticate() == before
    return {"status": "PASS", "authentication": before,
            "patch_classification": patch, "exterior_witnesses": witnesses,
            "formal_checks": checks,
            "sealed_reference_replay": reference,
            "I189_computational_seal": False,
            "local_ear_mechanism": "PARKED", "E183": "UNRESOLVED",
            "Z184": "UNRESOLVED"}, proc


if __name__ == "__main__":
    assert sys.flags.isolated and sys.dont_write_bytecode
    assert not sys.argv[1:]
    result, proc = replay()
    prefix = EXP / "i189-parent-verification"
    for suffix, data in ((".stdout", proc.stdout), (".stderr", proc.stderr)):
        with prefix.with_suffix(suffix).open("xb") as out:
            out.write(data)
    with prefix.with_suffix(".json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: I189 hashes, exhaustive patch classification, exterior "
          "witnesses and inherited replay",
          result["sealed_reference_replay"]["elapsed_seconds"], "seconds")
