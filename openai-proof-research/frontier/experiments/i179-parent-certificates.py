"""Independent DFS and edge-by-edge recoloring checks of the I179 lock."""
import hashlib
import json
import runpy
from itertools import product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT/"frontier/experiments/i179_path_recombination"
HELPER = BASE.parent/"i175-parent-certificates.py"
H = runpy.run_path(str(HELPER))
packings = H["packings"]


def read(path):
    return json.loads(path.read_bytes())


def main():
    old = read(BASE.parent/"i177_adjacent_port_surgery/experiment-attempt-03.json")
    report = read(BASE/"recombination-attempt-03.json")
    fresh = read(BASE/"analytic-attempt-03.json")["systems"][0]
    es = tuple(map(tuple,old["fiveport"]["xe"]))
    vertices = tuple(sorted({v for e in es for v in e}))
    boundary = (13,19,20,30,31)
    P = sorted(packings(es,vertices,((13,19),)))
    S = sorted(packings(es,vertices,((13,20),)))
    assert len(P) == 5 and len(S) == 1
    assert S == list(map(tuple,fresh["states"][0]["X"]))
    lost = next(r for r in fresh["complete"] if r["J"] == [0,1])
    assert P == list(map(tuple,lost["local"][0]["packings"]))

    def components(vector):
        adjacency = {v:set() for v in vertices}
        for (a,b),used in zip(es,vector):
            if used:
                adjacency[a].add(b)
                adjacency[b].add(a)
        unseen,result = set(vertices),[]
        while unseen:
            stack,seen = [min(unseen)],set()
            while stack:
                v = stack.pop()
                if v not in seen:
                    seen.add(v)
                    stack.extend(adjacency[v]-seen)
            unseen -= seen
            result.append(sorted(seen))
        return sorted(result)

    def degrees(vector):
        return {v:sum(x for e,x in zip(es,vector) if v in e) for v in vertices}

    def endpoints(vector):
        degree = degrees(vector)
        assert all(degree[v] == 2 for v in set(vertices)-set(boundary))
        assert all(degree[v] in (1,2) for v in boundary)
        return tuple(i for i,v in enumerate(boundary) if degree[v] == 1)

    totals = dict(overlays=5,components=0,cycle_obstructed=0,cycle_free=0)
    recolorings,edge_assignments,degree_assignments = [],0,0
    for pi,a in enumerate(P):
        b = S[0]
        difference = tuple(int(x != y) for x,y in zip(a,b))
        indices = [i for i,x in enumerate(difference) if x]
        comps = [c for c in components(difference) if len(c)>1]
        active = [{i for i in indices if es[i][0] in c} for c in comps]
        assert set().union(*active) == set(indices)
        # Independent completeness: try every difference EDGE assignment,
        # not only the component subsets used by the child's diagnostic.
        valid,degree_valid = set(),set()
        for bits in product((0,1),repeat=len(indices)):
            edge_assignments += 1
            aa,bb = list(a),list(b)
            for i,flip in zip(indices,bits):
                if flip:
                    aa[i],bb[i] = bb[i],aa[i]
            da,db = degrees(aa),degrees(bb)
            if any(da[v] != 2 or db[v] != 2 for v in set(vertices)-set(boundary)):
                continue
            if any(da[v] not in (1,2) or db[v] not in (1,2) for v in boundary):
                continue
            if {endpoints(aa),endpoints(bb)} != {(0,1),(0,2)}:
                continue
            degree_assignments += 1
            degree_valid.add((tuple(aa),tuple(bb)))
            if len(components(aa)) == len(components(bb)) == 1:
                valid.add((tuple(aa),tuple(bb)))
        assert valid == {(a,b),(b,a)}
        assert len(degree_valid) == 2**len(comps)
        allowed = []
        for mask in range(2**len(comps)):
            aa,bb = list(a),list(b)
            for j,cc in enumerate(active):
                if mask & (1<<j):
                    for i in cc:
                        aa[i],bb[i] = bb[i],aa[i]
            assert (tuple(aa),tuple(bb)) in degree_valid
            if (tuple(aa),tuple(bb)) in valid:
                allowed.append(mask)
            if mask and mask & (mask-1) == 0:
                totals["components"] += 1
                bad = any(all(degrees(v)[x] == 2 for x in c)
                          for v in (aa,bb) for c in components(v))
                totals["cycle_obstructed" if bad else "cycle_free"] += 1
        recolorings.append(dict(P_index=pi,components=len(comps),tested=2**len(comps),
                                admissible_masks=allowed,only_original_unordered_pair=True))
    assert recolorings == report["complete_recolorings"]
    assert totals == report["totals"]
    assert degree_assignments == 18 and totals["components"] == 9
    assert totals["cycle_obstructed"] == 8 and totals["cycle_free"] == 1
    obstruction = report["first_cycle_obstruction"]
    assert tuple(obstruction["a"]) == P[0] and tuple(obstruction["b"]) == S[0]
    changed = set(map(tuple,obstruction["exchanged_edges"]))
    assert changed == {(14,15),(14,22),(15,23),(22,23)}
    for name,other,out,words,desc in zip(
            ("a","b"),("b","a"),("output_a","output_b"),
            obstruction["output_words"],obstruction["output_components"]):
        vector = obstruction[out]
        assert vector == [obstruction[other][i] if e in changed else obstruction[name][i]
                          for i,e in enumerate(es)]
        assert components(vector) == desc["components"]
        assert degrees(vector) == {int(v):d for v,d in desc["degrees"].items()}
        assert list(endpoints(vector)) == desc["J"]
        assert desc["pairing"] == [desc["J"]]
        assert desc["isolated_cycles"] == [
            c for c in components(vector) if all(degrees(vector)[v] == 2 for v in c)]
        chosen = {tuple(sorted((a,b))) for w in words for a,b in zip(w,w[1:])}
        assert tuple(int(e in chosen) for e in es) == tuple(vector)
        assert sorted(v for w in words for v in (w[:-1] if w[0] == w[-1] else w)) == list(vertices)
    for v,words in zip((P[0],S[0]),obstruction["input_words"]):
        assert len(words) == 1 and sorted(words[0]) == list(vertices)
        selected = {tuple(sorted(e)) for e in zip(words[0],words[0][1:])}
        assert v == tuple(int(e in selected) for e in es)
    result = dict(status="PASS",method="Committed parent DFS/path partition helper; fresh edge-by-edge recoloring enumeration",
                  helper=str(HELPER.relative_to(ROOT)),helper_sha256=hashlib.sha256(HELPER.read_bytes()).hexdigest(),
                  complete_P=5,complete_state0=1,edge_assignments=edge_assignments,
                  degree_admissible_assignments=degree_assignments,totals=totals,
                  recolorings=recolorings,explicit_words_and_cycle_components="PASS",
                  limits="One retained local graph only. Inherited mathematical populations and 900 brace matchings replayed, not independently rescanned this round. L179 unresolved.")
    with (BASE.parent/"i179-parent-certificates.json").open("x") as out:
        json.dump(result,out,indent=2,sort_keys=True)
        out.write("\n")
    print("PASS: complete five P paths, sole state0 path, all18 degree-admissible recolorings and explicit isolated cycles")


if __name__ == "__main__":
    main()
