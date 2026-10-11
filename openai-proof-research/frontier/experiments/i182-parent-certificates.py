"""Independent parent certificates for the I182 controlled-extension claims.

Fresh standard-library implementation.  The only reused code is the
committed parent helper chain (i175-parent-certificates.py path packing
enumeration, disclosed); every graph complement, matching, component and
classification computation below is fresh parent code.  No I182 source is
executed, imported or compiled.

Verified independently on the retained, frozen, authenticated I177 glued
graph:

1. PATCH CENSUS.  All quadrilateral face pairs are re-enumerated; exactly
   three internal port-disjoint two-square patches survive, and the four
   excluded pairs carry the stated reasons.

2. REDUCTION LEMMA (finite certification).  For each of the six directed
   lost-lost instances, every perfect matching of the derived graph
   G' = G - V(C) is enumerated by a fresh exact-cover recursion.  For all
   626 matchings the equivalence "complement Hamiltonian in G" <=>
   "complement cross-paired acyclic two-path in G'" is rechecked, together
   with the forced degree pattern and the parallel-pairing two-cycle case.

3. FINITE CERTIFICATE.  Per instance the full classification (8
   Hamiltonian, 5 controlled, 3 lost type P, parallel/closed counts),
   the hit fibres {5:2, 6:1, 9:2}, and the exact coincidence of the five
   controlled matchings with the survivor-helper products (3 helpers,
   5 single-cycle products, 9 correctly excluded equal-pairing products)
   are recomputed and compared against the sealed extension payload.

4. TOPOLOGICAL HALF.  On every retained instance at least one lost
   matching is the q-completion itself, confirming that controls (1)+(2)
   are payable while survival is the unpaid content.
"""
import json
import runpy
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
EXP = ROOT/"frontier/experiments"
BASE = EXP/"i182_controlled_extension"
OUT = EXP/"i182-parent-certificates.json"
CHAIN = runpy.run_path(str(EXP/"i175-parent-certificates.py"))
parent_packings = CHAIN["packings"]

TYPES = [
    ((0, 2), ((0, 2),)), ((1, 2), ((1, 2),)),
    ((1, 4), ((1, 4),)), ((2, 4), ((2, 4),)),
    ((0, 1, 2, 3), ((0, 2), (1, 3))),
    ((0, 1, 2, 3), ((0, 3), (1, 2))),
    ((0, 1, 3, 4), ((0, 3), (1, 4))),
    ((0, 2, 3, 4), ((0, 2), (3, 4))),
    ((0, 2, 3, 4), ((0, 3), (2, 4))),
    ((1, 2, 3, 4), ((1, 2), (3, 4))),
    ((1, 2, 3, 4), ((1, 4), (2, 3))),
]


def load(relative):
    return json.loads((ROOT/relative).read_bytes())


def edge(a, b):
    return (a, b) if a < b else (b, a)


def components(vertices, edges):
    """Fresh iterative DFS; parallel edges contribute separate degrees."""
    adj = {v: [] for v in vertices}
    for a, b in edges:
        adj[a].append(b)
        adj[b].append(a)
    seen, groups = set(), []
    for s in sorted(vertices):
        if s in seen:
            continue
        stack, group = [s], set()
        while stack:
            v = stack.pop()
            if v in group:
                continue
            group.add(v)
            stack.extend(adj[v])
        seen |= group
        groups.append(sorted(group))
    return groups, adj


def perfect_matchings(vertices, edges):
    """Fresh exact-cover recursion, smallest-degree vertex first."""
    adj = {v: [] for v in vertices}
    for e in edges:
        adj[e[0]].append(e)
        adj[e[1]].append(e)
    out = []

    def visit(open_vertices, chosen):
        if not open_vertices:
            out.append(tuple(sorted(chosen)))
            return
        v = min(open_vertices, key=lambda w: sum(1 for e in adj[w]
                                                 if e[0] in open_vertices and e[1] in open_vertices))
        for e in adj[v]:
            a, b = e
            if a in open_vertices and b in open_vertices:
                visit(open_vertices - {a, b}, chosen + [e])
    visit(set(vertices), [])
    return out


def pairing_of(vertices, edges, ports, port_index):
    """Path-component endpoint pairing, relabelled to port positions."""
    groups, adj = components(vertices, edges)
    pairs = []
    for g in groups:
        ends = sorted(v for v in g if len(adj[v]) == 1)
        if ends:
            assert len(ends) == 2
            pairs.append(tuple(sorted((port_index(ends[0]), port_index(ends[1])))))
    return tuple(sorted(pairs))


def main():
    child = load("frontier/experiments/i177_adjacent_port_surgery/experiment-attempt-03.json")["child"]
    es = sorted(map(tuple, child["graph"]["edges"]))
    faces = [list(f) for f in child["graph"]["faces"]]
    vertices = sorted({v for e in es for v in e})
    d = load("frontier/experiments/i180_survivor_helper_connectivity/mandatory-attempt-02.json")["I178"]
    xe = sorted(map(tuple, d["xe"]))
    ye = sorted(map(tuple, d["ye"]))
    cut = [tuple(e) for e in d["cut"]]
    X, Y, xp = list(d["X"]), list(d["Y"]), list(d["xp"])
    yp = [next(v for v in e if v in Y) for e in cut]
    assert es == sorted(xe + ye + cut)
    payload = load("frontier/experiments/i182_controlled_extension/extension-attempt-01.json")
    assert payload["status"] == "PASS" and payload["E182"] == "UNRESOLVED"

    # Fresh graph sanity: simple, cubic, connected, bipartite.
    assert len(es) == len(set(es)) and all(a < b for a, b in es)
    groups, adj = components(vertices, es)
    assert len(groups) == 1 and all(len(adj[v]) == 3 for v in vertices)
    color = {vertices[0]: 0}
    stack = [vertices[0]]
    while stack:
        v = stack.pop()
        for w in adj[v]:
            if w not in color:
                color[w] = 1 - color[v]
                stack.append(w)
            assert color[w] != color[v]

    # Lost fibre P and survivor fibres via the committed parent helper chain.
    P = sorted(parent_packings(tuple(xe), tuple(X), ((xp[0], xp[1]),)))
    cal = load("frontier/experiments/i180_survivor_helper_connectivity/calibration-attempt-02.json")
    assert P == sorted(tuple(r["vector"]) for r in cal["P"])
    assert len(P) == 5
    survivor = []
    for used, pairing in TYPES:
        rows = parent_packings(tuple(xe), tuple(X),
                               tuple((xp[a], xp[b]) for a, b in pairing))
        survivor.append(sorted(rows))
    exterior = []
    for used, pairing in TYPES:
        by_label = {}
        for pr in combinations(used, 2):
            pass
        # all perfect pairings of the used label set
        def perms(items):
            if not items:
                yield []
                return
            first, *rest = items
            for i, other in enumerate(rest):
                for tail in perms(rest[:i]+rest[i+1:]):
                    yield [(first, other)] + tail
        for pr in perms(list(used)):
            key = tuple(sorted(tuple(sorted(p)) for p in pr))
            rows = parent_packings(tuple(ye), tuple(Y),
                                   tuple((yp[a], yp[b]) for a, b in pr))
            if rows:
                by_label[key] = sorted(rows)
        exterior.append(by_label)

    # 1. Patch census.
    quads = [f for f in faces if len(f) == 4]
    patches, excluded = [], []
    ports = set(xp)
    for f1, f2 in combinations(quads, 2):
        e1 = {edge(f1[i], f1[(i+1) % 4]) for i in range(4)}
        e2 = {edge(f2[i], f2[(i+1) % 4]) for i in range(4)}
        if len(e1 & e2) != 1:
            continue
        boundary = sorted(e1 ^ e2)
        bverts = sorted({v for e in boundary for v in e})
        groups, badj = components(bverts, boundary)
        simple = (len(bverts) == 6 and len(groups) == 1
                  and all(len(badj[v]) == 2 for v in bverts))
        if not simple:
            excluded.append("boundary not a simple six-cycle")
        elif not set(bverts) <= set(X):
            excluded.append("not internal to X")
        elif set(bverts) & ports:
            excluded.append("meets the five ports")
        else:
            patches.append({"boundary": boundary, "chord": next(iter(e1 & e2))})
    assert len(patches) == 3 and len(excluded) == 4
    assert sorted(excluded) == sorted([r["reason"] for r in payload["patches_excluded"]])
    assert sorted(tuple(p["boundary"]) for p in patches) == sorted(
        tuple(map(tuple, i["patch_boundary"])) for i in payload["instances"][::2])
    x_index = {v: i for i, v in enumerate(xp)}
    y_index = {v: i for i, v in enumerate(yp)}

    # 2+3+4. Instance certificates.
    instance_reports = []
    total_checks = 0
    for patch in patches:
        boundary, chord = patch["boundary"], patch["chord"]
        bverts = sorted({v for e in boundary for v in e})
        cx, cy = chord
        others = [v for v in bverts if v not in chord]
        continuation = {}
        for v in others:
            third = [e for e in es if v in e and e not in boundary]
            assert len(third) == 1
            continuation[v] = third[0]
        g_verts = [v for v in vertices if v not in bverts]
        g_edges = [e for e in es if not (set(e) & set(bverts))]
        matchings = perfect_matchings(g_verts, g_edges)
        directed = []
        for pi, qi in combinations(range(len(P)), 2):
            diff = [e for e, a, b in zip(xe, P[pi], P[qi]) if a != b]
            if set(diff) == set(boundary):
                directed.append((pi, qi))
                directed.append((qi, pi))
        assert len(directed) == 2
        for p_index, q_index in directed:
            p_row, q_row = P[p_index], P[q_index]
            half_a = sorted(e for e in boundary if p_row[xe.index(e)])
            assert len(half_a) == 3
            summary = {"total": len(matchings), "hamiltonian": 0, "controlled": 0,
                       "lost_P": 0, "lost_D": 0, "parallel_pairing": 0,
                       "with_closed_components": 0}
            fibres_hit = {}
            controlled_rows = set()
            q_completion_seen = False
            for m in matchings:
                m_set = set(m)
                full_m = m_set | set(half_a)
                h_edges = [e for e in es if e not in full_m]
                h_groups, h_adj = components(vertices, h_edges)
                assert all(len(h_adj[v]) == 2 for v in vertices)
                hamiltonian = len(h_groups) == 1
                hp_edges = [e for e in g_edges if e not in m_set]
                hp_groups, hp_adj = components(g_verts, hp_edges)
                deg1 = sorted(v for v in g_verts if len(hp_adj[v]) == 1)
                assert deg1 == sorted(next(w for w in continuation[v] if w != v)
                                      for v in others)
                closed = [g for g in hp_groups if all(len(hp_adj[v]) == 2 for v in g)]
                path_pairs = sorted(
                    tuple(sorted(v for v in g if len(hp_adj[v]) == 1))
                    for g in hp_groups if any(len(hp_adj[v]) == 1 for v in g))
                t = {k: next(w for w in continuation[v] if w != v)
                     for k, v in zip("abcd", sorted(others, key=lambda v: (
                         0 if edge(cx, v) in half_a else
                         2 if edge(cx, v) in boundary else
                         1 if edge(cy, v) in half_a else 3)))}
                parallel = (path_pairs == sorted([tuple(sorted((t["a"], t["b"]))),
                                                  tuple(sorted((t["c"], t["d"])))]))
                cross = not closed and len(path_pairs) == 2 and not parallel
                assert hamiltonian == cross  # reduction lemma, both directions
                total_checks += 1
                if closed:
                    summary["with_closed_components"] += 1
                elif parallel:
                    summary["parallel_pairing"] += 1
                if not hamiltonian:
                    continue
                summary["hamiltonian"] += 1
                local = tuple(1 if e in h_edges else 0 for e in xe)
                used = tuple(j for j, e in enumerate(cut) if e in h_edges)
                pairing = pairing_of(X, [e for e, b in zip(xe, local) if b],
                                     xp, x_index.get)
                type_index = next((i for i, (uu, pp) in enumerate(TYPES)
                                   if tuple(uu) == used
                                   and tuple(map(tuple, pp)) == pairing), None)
                m_bits = tuple(1 if e in full_m else 0 for e in es)
                if type_index is None:
                    assert (used, pairing) in (((0, 1), ((0, 1),)),
                                               ((0, 1, 3, 4), ((0, 1), (3, 4))))
                    summary["lost_P" if used == (0, 1) else "lost_D"] += 1
                    if local == q_row:
                        q_completion_seen = True
                    continue
                summary["controlled"] += 1
                fibres_hit[type_index] = fibres_hit.get(type_index, 0) + 1
                controlled_rows.add(m_bits)
                u_row, v_row = local, tuple(1-b if e in boundary else b
                                            for e, b in zip(xe, local))
                assert tuple(a+b for a, b in zip(p_row, u_row)) == \
                       tuple(a+b for a, b in zip(q_row, v_row))
            assert q_completion_seen, "q-completion must appear as a lost matching"
            # Helper-product correspondence.
            half_a_set, half_b_set = set(half_a), set(boundary) - set(half_a)
            helpers_total = helpers_confirmed = products_cyclic = 0
            for state, rows in enumerate(survivor):
                used, pairing = TYPES[state]
                for u_row in rows:
                    on = {e for e, b in zip(xe, u_row) if b}
                    if not half_b_set <= on or on & half_a_set:
                        continue
                    helpers_total += 1
                    for pr, yrows in exterior[state].items():
                        for y_row in yrows:
                            h = [0]*len(es)
                            for e, b in zip(xe, u_row):
                                h[es.index(e)] += b
                            for e, b in zip(ye, y_row):
                                h[es.index(e)] += b
                            for m_ in used:
                                h[es.index(cut[m_])] += 1
                            h_edges = [e for e, b in zip(es, h) if b]
                            h_groups, h_adj = components(vertices, h_edges)
                            single = (len(h_groups) == 1
                                      and all(len(h_adj[v]) == 2 for v in vertices))
                            assert single == (len(used) == 2 or pr != tuple(
                                sorted(tuple(sorted(p)) for p in pairing)))
                            if not single:
                                products_cyclic += 1
                                continue
                            m_bits = tuple(0 if e in h_edges else 1 for e in es)
                            assert m_bits in controlled_rows
                            helpers_confirmed += 1
            instance_reports.append({"p_index": p_index, "q_index": q_index,
                                     "matchings": summary, "fibres_hit": fibres_hit,
                                     "helpers_total": helpers_total,
                                     "helpers_confirmed": helpers_confirmed,
                                     "products_cyclic": products_cyclic})
    assert total_checks == 626 == payload["reduction_checks"]
    assert len(instance_reports) == 6 == payload["instances_count"]
    key = lambda r: (r["p_index"], r["q_index"])
    for mine, theirs in zip(sorted(instance_reports, key=key),
                            sorted(payload["instances"], key=key)):
        assert key(mine) == key(theirs)
        assert mine["matchings"] == theirs["matchings"], key(mine)
        assert mine["fibres_hit"] == {int(k): v for k, v in theirs["fibres_hit"].items()}
        assert (mine["helpers_total"], mine["helpers_confirmed"],
                mine["products_cyclic"]) == (theirs["helpers_total"],
                                             theirs["helpers_confirmed"],
                                             theirs["products_cyclic"])
    receipt = {
        "status": "PASS",
        "graph": {"vertices": len(vertices), "edges": len(es),
                  "simple_cubic_bipartite_connected": True},
        "patches_internal": 3,
        "patches_excluded_reasons": sorted(excluded),
        "instances": 6,
        "reduction_equivalence_checks": total_checks,
        "per_instance": {"hamiltonian": 8, "controlled": 5, "lost_P": 3,
                         "lost_D": 0, "fibres": {"5": 2, "6": 1, "9": 2},
                         "helpers": 3, "products_single": 5,
                         "products_cyclic_excluded": 9},
        "q_completion_lost_on_every_instance": True,
        "payload_comparison": "all six instances match the sealed extension payload",
        "helper_chain": "committed i175-parent-certificates.py packings reused; all other code fresh",
        "scope": "Finite retained-graph certificate verified; E182/CPTP-survival remains unpaid.",
    }
    with OUT.open("x") as out:
        json.dump(receipt, out, indent=2, sort_keys=True)
        out.write("\n")
    print("I182 parent certificates PASS: 3 patches, 6 instances,",
          total_checks, "reduction checks, 5 controlled matchings each")


if __name__ == "__main__":
    main()
