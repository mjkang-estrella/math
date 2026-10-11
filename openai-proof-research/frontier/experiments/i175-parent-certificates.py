"""Parent DFS and exact-rank checks of new graphs, packings and boundary examples."""
import hashlib
import json
import runpy
from collections import Counter
from functools import lru_cache
from itertools import combinations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i175_affected_prism_exterior"
HELPER = BASE.parent / "i174-parent-certificates.py"
H = runpy.run_path(str(HELPER))
edge, paths, cycles, rank, differences, minus = (
    H[k] for k in ("edge", "paths", "cycles", "rank", "differences", "minus"))


def read(name):
    return json.loads((BASE / name).read_bytes())


def vec(es, selected):
    return tuple(int(e in selected) for e in es)


@lru_cache(None)
def packings(es, vertices, pairs):
    vertices = set(vertices)
    if len(pairs) == 1:
        return frozenset(vec(es, p) for p in paths(es, *pairs[0], vertices))
    (a, b), (c, d) = pairs
    result = set()
    for p in paths(es, a, b, vertices - {c, d}, spanning=False):
        used = {v for e in p for v in e}
        for q in paths(es, c, d, vertices - used):
            result.add(vec(es, p | q))
    return frozenset(result)


def main():
    exp = read("experiment-attempt-01.json")
    local = read("local_saturation-attempt-01.json")["certificates"]
    boundary = read("boundary-attempt-03.json")
    assert len(exp["plan"]["valid"]) == 14 and len(exp["plan"]["untested"]) == 12
    assert Counter(z["reason"] for z in exp["plan"]["skips"]) == {
        "bipartite-orientation": 14, "protected-perimeter": 4}
    assert exp["second_attachments"] == exp["second_surgeries"] == 0
    new_rows = []
    for r in [exp["initial"]] + exp["first_children"]:
        H["families"](r)
        g = r["graph"]
        es = list(map(tuple, g["edges"]))
        vertices = {v for e in es for v in e}
        expected_pairs = {(i, j) for i, j in combinations(range(len(es)), 2)
                          if not set(es[i]) & set(es[j])}
        seen = set()
        for i, j, matching in r["brace"]["extensions"]:
            assert (i, j) not in seen and i in matching and j in matching
            assert len(matching) == len(set(matching)) and all(0 <= k < len(es) for k in matching)
            assert Counter(v for k in matching for v in es[k]) == Counter({v: 1 for v in vertices})
            seen.add((i, j))
        failed = set(map(tuple, r["brace"]["failures"]))
        assert seen.isdisjoint(failed) and seen | failed == expected_pairs
        if failed:
            side = set(range(13, 28))
            cut = [i for i, e in enumerate(es) if len(set(e) & side) == 1]
            assert failed == set(combinations(cut, 2))
            # The punctured P8 side has imbalance one and majority-colour ports.
            colors = {12+i: (i % 2 if i < 8 else 1-(i-8) % 2) for i in range(1, 16)}
            ports = [next(v for v in es[k] if v in side) for k in cut]
            assert all(colors[v] == 1 for v in ports)
            assert sum(1 if colors[v] == 1 else -1 for v in side) == 1
        else:
            assert len(seen) == 900
        new_rows.append(dict(n=g["n"], rankL=r["row"]["rankL"], loss=r["row"]["ell"],
                             matchings=len(seen), failures=len(failed), brace=not failed))

    old = json.loads((ROOT / "frontier/experiments/i174_prism_gadget_survival/structural-attempt-03.json").read_bytes())["applications"]
    records = [old[i]["contracted"] for i in (2, 3, 0, 1)] + exp["first_children"]
    checks = []
    for c, r in zip(local, records):
        assert c["graph"]["edges"] == r["graph"]["edges"]
        es = list(map(tuple, c["graph"]["edges"]))
        les, yes, cut = (list(map(tuple, c[k])) for k in ("local_edges", "exterior_edges", "cut"))
        side, outside = set(c["side"]), set(c["outside"])
        assert side.isdisjoint(outside) and len(outside) == 13 and len(side) == 2*c["k"]+1
        assert len(cut) == 5 and set(es) == set(les) | set(yes) | set(cut)
        assert len(les) == 3*c["k"]-1
        endpoint = [{i: next(v for v in e if v in part) for i, e in enumerate(cut)}
                    for part in (side, outside)]
        u, v, x, y = r["uvxy"]
        ei, fi = cut.index(edge(u, v)), yes.index(edge(x, y))
        def lift(a, b, chosen):
            coords = dict(zip(les, a))
            coords.update(zip(yes, b))
            coords.update({e: int(i in chosen) for i, e in enumerate(cut)})
            return tuple(coords[e] for e in es)
        all_survivors, WX, WY, anchors = set(), [], [], []
        for state in c["states"]:
            pairs = [tuple((endpoint[j][a], endpoint[j][b]) for a, b in state[k])
                     for j, k in enumerate(("local_pairing", "exterior_pairing"))]
            aa = sorted(packings(tuple(les), tuple(sorted(side)), pairs[0]))
            bb0 = sorted(packings(tuple(yes), tuple(sorted(outside)), pairs[1]))
            bb = [b for b in bb0 if ei in state["cut"] or b[fi]]
            assert aa == list(map(tuple, state["local_packings"])) and bb == list(map(tuple, state["exterior_packings"]))
            anchor = lift(aa[0], bb[0], state["cut"])
            assert anchor == tuple(state["anchor"])
            anchors.append(anchor)
            WX.extend(minus(lift(a, bb[0], state["cut"]), anchor) for a in aa[1:])
            WY.extend(minus(lift(aa[0], b, state["cut"]), anchor) for b in bb[1:])
            lifted = {lift(a, b, state["cut"]) for a, b in product(aa, bb)}
            assert not all_survivors & lifted and len(lifted) == state["product_size"]
            all_survivors |= lifted
        fresh_cycles = cycles(es, side | outside)
        genuine = {vec(es, hc) for hc in fresh_cycles if edge(u, v) in hc or edge(x, y) in hc}
        assert all_survivors == genuine
        A = differences(anchors)
        a, b, full = rank(WX), rank(WY), rank(WX + WY + A)
        projected = [i for i, e in enumerate(es) if e not in les]
        image = rank([[z[i] for i in projected] for z in WY + A])
        assert [a, b, full-a-b, full, image, full-image, full-image-a] == [
            c[k] for k in ("local_rank", "exterior_rank", "anchor_quotient_rank",
                          "survivor_rank", "image_rank", "kernel_rank", "extra_anchor_kernel")]
        assert full == len(es)-len(side)-len(outside)+1
        checks.append(dict(k=c["k"], states=len(c["states"]), survivors=len(genuine),
                           local_rank=a, exterior_rank=b, anchor_increment=full-a-b,
                           image=image, kernel=full-image, extra_anchor_kernel=full-image-a))
    w = boundary["proper_type_counterexample"]
    g, h = w["graph"], w["exterior"]
    def cycle_vectors(graph):
        edges = list(map(tuple, graph["edges"]))
        return sorted(vec(edges, z) for z in cycles(edges, {v for e in edges for v in e}))
    gc, hc = cycle_vectors(g), cycle_vectors(h)
    assert set(map(tuple, w["survivors"])) <= set(gc) and set(map(tuple, w["exterior_members"])) <= set(hc)
    assert rank(differences(hc))-rank(differences(w["exterior_members"])) == w["ellH"] == 4
    assert rank(differences(gc))-rank(differences(w["survivors"])) == w["ellG"] == 6
    incomplete = boundary["incomplete_fibres"]
    assert set(map(tuple, incomplete["full_cycles"])) == set(gc)
    assert rank(differences(gc)) == 8 and rank(differences(incomplete["restricted_cycles"])) == 5
    tetra = boundary["all_three_not_necessary"]
    assert cycle_vectors(tetra["attachment"]) == list(map(tuple, tetra["cycles"]))
    assert len(tetra["cycles"]) == 3
    assert boundary["boundary_scan"]["interface_vertex_cases"] == 720
    assert not boundary["boundary_scan"]["missing_type_records"]
    result = dict(status="PASS", new_graphs=new_rows, five_port_checks=checks,
                  missing_type_losses=[4, 6], incomplete_fibre_dimensions=[8, 5],
                  method="Parent-only DFS, direct product reconstruction, independent Fraction ranks and matching certificates",
                  parent_helper=str(HELPER.relative_to(ROOT)), helper_sha256=hashlib.sha256(HELPER.read_bytes()).hexdigest(),
                  limits="The 720-record boundary scan is covered by sealed replay, not a separate parent rescan; no infinite k claim.")
    with (BASE.parent / "i175-parent-certificates.json").open("x") as out:
        json.dump(result, out, indent=2, sort_keys=True)
        out.write("\n")
    print("PASS: three complete seven-family graphs, 2460 matchings, six exhaustive five-port products, missing-type examples")


if __name__ == "__main__":
    main()
