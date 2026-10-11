"""Independent parent certificates for the I181 two-square six-cycle claims.

Fresh standard-library implementation; no I181 source is executed, imported
or compiled.  Three independent checks:

1. PATCH FORCING.  On the abstract two-face patch (six-cycle plus chord plus
   four continuation edges, all six cycle vertices internally cubic), exhaust
   all 2^11 local edge subsets with correct internal degrees.  Verify that a
   subset whose cycle restriction equals one alternating half is unique,
   forced to contain the chord and all four continuation edges, and that both
   halves induce the same pairing on the four continuation terminals.

2. REATTACHMENT INVARIANCE.  Independently enumerate every external perfect
   segment pairing on the combined terminal set (both port arities the child
   used), and verify that reattaching with either alternating half preserves
   the cyclic-component count and the external port pairing, with loops and
   parallel two-edge components retained.  Compare the full recomputed table
   byte-exactly against the retained sealed topology payload.

3. REPORT CONSTANTS.  Verify the routings quoted in the report and the
   retained payload row count against independent enumeration.
"""
import hashlib
import itertools
import json
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/"frontier/experiments/i181_six_cycle_helper"
OUT = BASE.parent/"i181-parent-certificates.json"

# Patch vertices: x=0, a=1, b=2, y=3, d=4, c=5; terminals ta=6, tb=7, td=8, tc=9.
CYCLE = [(0, 1), (1, 2), (2, 3), (3, 4), (4, 5), (0, 5)]
HALF_A = [(0, 1), (2, 3), (4, 5)]
HALF_B = [(1, 2), (3, 4), (0, 5)]
CHORD = (0, 3)
CONT = [(1, 6), (2, 7), (4, 8), (5, 9)]
EDGES = sorted(set(CYCLE) | {CHORD} | set(CONT))
INTERNAL = [0, 1, 2, 3, 4, 5]
TERMINALS = [6, 7, 8, 9]


def canonical(value):
    return json.dumps(value, sort_keys=True, separators=(",", ":")).encode()


def components_with_degree(vertices, edges):
    """Components plus per-vertex degree counting parallel edges distinctly."""
    parent = {v: v for v in vertices}

    def find(v):
        while parent[v] != v:
            parent[v] = parent[parent[v]]
            v = parent[v]
        return v

    deg = {v: 0 for v in vertices}
    for a, b in edges:
        deg[a] += 1
        deg[b] += 1
        ra, rb = find(a), find(b)
        if ra != rb:
            parent[ra] = rb
    groups = {}
    for v in vertices:
        groups.setdefault(find(v), []).append(v)
    return [sorted(g) for g in groups.values()], deg


def pairing_on(groups, deg, ports):
    """Pairing induced on ports by non-singleton path components."""
    out = []
    for g in groups:
        ends = sorted(v for v in g if deg[v] == 1)
        on_ports = sorted(v for v in g if v in ports)
        if on_ports:
            assert len(ends) == 2 and ends == on_ports or deg[on_ports[0]] == 1
            out.append(tuple(on_ports))
    return sorted(out)


def patch_forcing():
    results = {}
    index = {e: i for i, e in enumerate(EDGES)}
    for half_name, half in (("A", HALF_A), ("B", HALF_B)):
        half_set = set(half)
        solutions = []
        for bits in range(1 << len(EDGES)):
            chosen = [EDGES[i] for i in range(len(EDGES)) if bits >> i & 1]
            on_cycle = [e for e in chosen if e in CYCLE]
            if set(on_cycle) != half_set:
                continue
            vertices = sorted({v for e in chosen for v in e} | set(INTERNAL))
            _, deg = components_with_degree(vertices, chosen)
            if any(deg[v] != 2 for v in INTERNAL):
                continue
            solutions.append(tuple(EDGES[i] for i in range(len(EDGES)) if bits >> i & 1))
        # Exactly one degree-correct local restriction uses this half.
        assert len(solutions) == 1, (half_name, len(solutions))
        (solution,) = solutions
        assert CHORD in solution and all(e in solution for e in CONT)
        vertices = sorted({v for e in solution for v in e})
        groups, deg = components_with_degree(vertices, list(solution))
        # No cyclic component locally, and the terminal pairing is ta-tb, tc-td.
        assert all(any(deg[v] != 2 for v in g) for g in groups)
        assert pairing_on(groups, deg, TERMINALS) == [(6, 7), (8, 9)]
        results[half_name] = {"solution": [list(e) for e in solution],
                              "terminal_pairing": [[6, 7], [8, 9]]}
    # Both halves force the same chord, continuations and terminal pairing.
    cont_a = {tuple(e) for e in results["A"]["solution"]} & set(CONT)
    cont_b = {tuple(e) for e in results["B"]["solution"]} & set(CONT)
    assert cont_a == cont_b == set(CONT)
    # Routings quoted in the report (walks from the smaller endpoint).
    routing_a = sorted(map(sorted, components_with_degree(range(6), HALF_A + [CHORD])[0]))
    routing_b = sorted(map(sorted, components_with_degree(range(6), HALF_B + [CHORD])[0]))
    assert routing_a == [[0, 1, 2, 3], [4, 5]] and routing_b == [[0, 3, 4, 5], [1, 2]]
    return results


def pairings(items):
    if not items:
        yield []
        return
    first, *rest = items
    for i, other in enumerate(rest):
        for tail in pairings(rest[:i] + rest[i + 1:]):
            yield [(first, other)] + tail


def reattachment_table():
    rows = []
    for ports in ([6, 7], [6, 7, 8, 9]):
        nodes = [1, 2, 4, 5] + ports
        for segments in pairings(nodes):
            quotient = list(segments) + [(1, 2), (4, 5)]
            groups, deg = components_with_degree(nodes, quotient)
            cyclic = [g for g in groups if all(deg[v] == 2 for v in g)]
            port_pairing = pairing_on(groups, deg, ports)
            reattachments = []
            for half in (HALF_A, HALF_B):
                edges = list(segments) + half + [CHORD]
                gs, dd = components_with_degree(sorted({0, 3} | set(nodes)), edges)
                cyc = sum(all(dd[v] == 2 for v in g) for g in gs)
                pp = pairing_on(gs, dd, ports)
                assert cyc == len(cyclic) and pp == port_pairing
                reattachments.append({"cycles": cyc, "pairing": pp})
            rows.append({"ports": ports, "segments": segments,
                         "quotient_cycles": len(cyclic), "pairing": port_pairing,
                         "reattachments": reattachments})
    # Explicit unsimplified contractions: a loop and a parallel pair are cycles.
    for es in ([(1, 1)], [(1, 2), (1, 2)]):
        vs = sorted({v for e in es for v in e})
        gs, dd = components_with_degree(vs, es)
        assert len(gs) == 1 and all(dd[v] == 2 for v in vs)
    return rows


def main():
    forcing = patch_forcing()
    rows = reattachment_table()
    assert len(rows) == 15 + 105
    retained = json.loads((BASE/"topology-attempt-01.json").read_bytes())
    retained.pop("runtime_seconds", None)
    assert retained["status"] == "PASS" and retained["E181"] == "UNRESOLVED"
    assert retained["rows_count"] == len(rows)
    assert canonical(retained["rows"]) == canonical(rows), "retained topology table mismatch"
    assert retained["routing_A"] == [[1, 0, 3, 2], [4, 5]]
    assert retained["routing_B"] == [[1, 2], [4, 3, 0, 5]]
    # Independent walk check of the two quoted routings.
    for half, expected in ((HALF_A, [[1, 0, 3, 2], [4, 5]]), (HALF_B, [[1, 2], [4, 3, 0, 5]])):
        adj = {v: [] for v in range(6)}
        for a, b in half + [CHORD]:
            adj[a].append(b)
            adj[b].append(a)
        walks = []
        for start in sorted(v for v in range(6) if len(adj[v]) == 1):
            if any(start == w[-1] for w in walks):
                continue
            word, at = [start], start
            while True:
                nxt = next(w for w in adj[at] if w not in word)
                word.append(nxt)
                at = nxt
                if len(adj[at]) != 2:
                    break
            walks.append(word)
        assert walks == expected
    payload = {
        "status": "PASS",
        "patch_forcing": forcing,
        "uniqueness": "exactly one degree-correct local restriction per alternating half",
        "reattachment_rows": len(rows),
        "retained_topology_table": "byte-identical recomputation",
        "topology_payload_sha256": hashlib.sha256(
            (BASE/"topology-attempt-01.json").read_bytes()).hexdigest(),
        "scope": "Formal local reattachment lemma verified; helper existence remains unpaid.",
    }
    with OUT.open("x") as out:
        json.dump(payload, out, indent=2, sort_keys=True)
        out.write("\n")
    print("I181 parent certificates PASS:", len(rows), "reattachment rows;",
          "unique forced restriction per half")


if __name__ == "__main__":
    main()
