"""Parent-only graph/path enumeration, exact ranks and absorption identities."""
import hashlib
import json
import runpy
from collections import Counter
from fractions import Fraction
from itertools import combinations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i177_adjacent_port_surgery"
HELPER = BASE.parent / "i175-parent-certificates.py"
H = runpy.run_path(str(HELPER))
edge, packings, cycles, rank, differences, minus = (
    H[k] for k in ("edge", "packings", "cycles", "rank", "differences", "minus"))
DET_HELPER = BASE.parent / "i176-parent-certificates.py"
det = runpy.run_path(str(DET_HELPER))["det"]


def vec(es, chosen):
    return tuple(int(e in chosen) for e in es)


def combination(rows, coeff):
    assert len(rows) == len(coeff)
    return tuple(sum(Fraction(a)*r[i] for a, r in zip(coeff, rows))
                 for i in range(len(rows[0])))


def graph_check(graph):
    es = list(map(tuple, graph["edges"]))
    vv = {v for e in es for v in e}
    adj = {v: {w for e in es if v in e for w in e if w != v} for v in vv}
    assert len(vv) == graph["n"] and es == sorted(set(es))
    assert all(a < b for a,b in es) and all(len(ns) == 3 for ns in adj.values())
    def reached(keep):
        seen = {min(keep)}
        todo = list(seen)
        while todo:
            for v in (adj[todo.pop()] & keep)-seen:
                seen.add(v)
                todo.append(v)
        return seen
    assert reached(vv) == vv
    for a,b in combinations(vv,2):
        assert reached(vv-{a,b}) == vv-{a,b}
    colors = {min(vv): 0}
    todo = list(colors)
    while todo:
        a = todo.pop()
        for b in adj[a]:
            if b not in colors:
                colors[b] = 1-colors[a]
                todo.append(b)
            assert colors[a] != colors[b]
    darts, links = Counter(), {v:{} for v in vv}
    for f in graph["faces"]:
        assert len(f) == len(set(f))
        for i,v in enumerate(f):
            w = f[(i+1) % len(f)]
            darts[v,w] += 1
            assert f[i-1] not in links[v]
            links[v][f[i-1]] = w
    assert darts == Counter(d for a,b in es for d in ((a,b),(b,a)))
    assert len(vv)-len(es)+len(graph["faces"]) == 2
    for v, link in links.items():
        a = min(adj[v])
        assert {a,link[a],link[link[a]]} == adj[v] and link[link[link[a]]] == a
    return es, vv


def main():
    payload = json.loads((BASE/"experiment-attempt-03.json").read_bytes())
    old, child, fp = (payload[k] for k in ("initial","child","fiveport"))
    oes, ov = graph_check(old["graph"])
    es, vv = graph_check(child["graph"])
    assert set(es) == set(oes)-{(1,2),(13,14)} | {
        (1,28),(2,29),(13,30),(14,31),(28,29),(28,30),(29,31),(30,31)}
    assert [1,13,21,20,6,7] in child["graph"]["faces"]
    for record in (old, child):
        H["H"]["families"]({**record, "bridge":record["b"]})
        assert set(map(tuple, record["cycles"])) == set(
            vec(list(map(tuple,record["graph"]["edges"])), c)
            for c in cycles(list(map(tuple,record["graph"]["edges"])),
                            {v for e in record["graph"]["edges"] for v in e}))
    assert payload["new_operations"] == 1
    assert payload["second_attachments"] == payload["second_surgeries"] == 0
    covered = set()
    for i,j,matching in child["brace"]["extensions"]:
        assert (i,j) not in covered and i in matching and j in matching
        assert len(matching) == len(set(matching))
        assert Counter(v for k in matching for v in es[k]) == Counter({v:1 for v in vv})
        covered.add((i,j))
    assert covered == {(i,j) for i,j in combinations(range(len(es)),2) if not set(es[i]) & set(es[j])}
    assert len(covered) == 900 and not child["brace"]["failures"]
    X,Y = set(fp["X"]),set(fp["Y"])
    xe,ye,cut = (list(map(tuple,fp[k])) for k in ("xe","ye","cut"))
    assert X == set(range(13,28)) | {30,31} and Y == set(range(1,12)) | {28,29}
    assert xe == [e for e in es if set(e) <= X] and ye == [e for e in es if set(e) <= Y]
    assert cut == [(1,13),(5,19),(6,20),(28,30),(29,31)]
    assert set(es) == set(xe+ye+cut)
    # Independently enumerate even used sets and all one/two-path pairings.
    families = {}
    for size in (2,4):
        for J in combinations(range(5),size):
            pairings = [((J[0],J[1]),)] if size == 2 else [
                ((J[0],J[i]),tuple(j for j in J if j not in (J[0],J[i]))) for i in (1,2,3)]
            groups = []
            for ee,side,end in ((xe,X,[e[1] for e in cut]),(ye,Y,[e[0] for e in cut])):
                d = {}
                for pairing in pairings:
                    rows = packings(tuple(ee),tuple(sorted(side)),
                                    tuple((end[a],end[b]) for a,b in pairing))
                    if rows:
                        d[tuple(sorted(pairing))] = sorted(rows)
                groups.append(d)
            families[J] = groups
    assert len(fp["all_families"]) == len(families) == 15
    for record in fp["all_families"]:
        for key, fresh in zip(("local","exterior"),families[tuple(record["J"])]):
            assert fresh == {tuple(map(tuple,g["pairing"])):list(map(tuple,g["packings"])) for g in record[key]}
    def lift(x,y,J):
        return vec(es, {e for e,a in zip(xe,x) if a} | {e for e,a in zip(ye,y) if a}
                   | {cut[i] for i in J})
    expected_states = {}
    for J,(xx,yy) in families.items():
        for px,xf in xx.items():
            for py,yf in yy.items():
                if len(J) == 4 and px == py:
                    continue
                yf = [y for y in yf if 2 in J or y[ye.index((1,7))]]
                if yf:
                    expected_states[J,px,py] = xf,yf
    products, WX, WY, anchors = set(),[],[],[]
    assert len(fp["states"]) == len(expected_states) == 11
    for st in fp["states"]:
        J,px,py = tuple(st["J"]),tuple(map(tuple,st["px"])),tuple(map(tuple,st["py"]))
        xx,yy = expected_states[J,px,py]
        assert xx == list(map(tuple,st["X"])) and yy == list(map(tuple,st["Y"]))
        anchor = lift(xx[0],yy[0],J)
        assert anchor == tuple(st["anchor"])
        anchors.append(anchor)
        actual = {lift(x,y,J) for x,y in product(xx,yy)}
        assert actual == set(map(tuple,st["products"])) and not products & actual
        products |= actual
        WX.extend(minus(lift(x,yy[0],J),anchor) for x in xx[1:])
        WY.extend(minus(lift(xx[0],y,J),anchor) for y in yy[1:])
    genuine = {tuple(r) for r in child["cycles"] if r[es.index((6,20))] or r[es.index((1,7))]}
    assert genuine == products == set(map(tuple,fp["survivors"])) and len(genuine) == 46
    A = differences(anchors)
    pi = [es.index(e) for e in ye+cut]
    assert rank(WX) == 5 and rank(WY) == 3 and rank(WX+WY+A) == 16
    assert rank([[r[i] for i in pi] for r in WY+A]) == 9
    local = list(map(tuple,fp["local_basis"]))
    outer = list(map(tuple,fp["exterior_basis"]))
    assert rank(local) == rank(WX+local) == 5 and rank(outer) == rank(WY+outer) == 3
    for w in payload["basis_witnesses"]:
        st = fp["states"][w["state"]]
        side = w["side"]
        ee = xe if side == "X" else ye
        d = dict(zip(ee, minus(st[side][w["packing"]],st[side][w["base"]])))
        assert tuple(d.get(e,0) for e in es) == tuple(w["direction"])
        assert w["common_partner"] == st["Y" if side == "X" else "X"][0]
    K = [combination([A[5],A[0],A[1],A[4]],[1,1,-1,-1]),
         combination([A[7],A[0],A[2],A[4]],[1,1,-1,-1])]
    assert all(not any(r[i] for i in pi) for r in K)
    assert rank(local+K) == 7
    assert K == [tuple(map(Fraction,r["direction"])) for r in fp["extra_kernel_relations"]]
    ambient = local+outer+[A[i-1] for i in (1,2,3,4,5,7)]+K
    assert ambient == [tuple(map(Fraction,r)) for r in payload["actual_ambient_basis"]]
    assert rank(ambient) == 16
    sb = list(map(tuple,child["survivor_basis"]))
    common = tuple(child["survivor_anchor"])
    assert common in genuine and len(sb) == rank(sb) == 16
    assert all(tuple(a+b for a,b in zip(common,r)) in genuine for r in sb)
    cert = payload["actual_survivor_minor"]
    matrix = [[r[i] for i in cert["columns"]] for r in sb]
    assert matrix == cert["matrix"] and det(matrix) == Fraction(cert["determinant"]) == 2
    oldS = sorted(old["families"]["N10"]+old["families"]["N01"]+old["families"]["N11"])
    D = [tuple(a["old_direction"]) for a in payload["old_defect_absorption"]]
    assert all(r in differences(old["cycles"]) for r in D)
    assert rank(differences(oldS)) == 11 and rank(differences(oldS)+D) == 14
    def transport(r):
        out = dict(zip(oes,r))
        a,b = out.pop((1,2)),out.pop((13,14))
        out.update({(1,28):a,(2,29):a,(13,30):b,(14,31):b,
                    (28,29):-a,(30,31):-b,(28,30):0,(29,31):0})
        v = tuple(out[e] for e in es)
        assert all(sum(z for e,z in zip(es,v) if t in e) == 0 for t in vv)
        return v
    # Injection checked on a full old-kernel basis, not only three selected vectors.
    full_old = list(map(tuple,old["survivor_basis"]))+D
    assert rank(full_old) == rank(list(map(transport,full_old))) == 14
    Z = list(map(transport,D))
    for z,rec in zip(Z,payload["old_defect_absorption"]):
        assert z == tuple(rec["transport"]) == combination(ambient,rec["coefficients"])
    assert Z[0] == combination(ambient,["25/6"]+["-5/6"]*4+[-3,1,1,1,1,-2,4,-5,1,"5/6","-5/6"])
    assert minus(Z[1],Z[0]) == outer[1] and minus(Z[2],Z[0]) == outer[2]
    def squares(ee):
        adj = {v:{w for e in ee if v in e for w in e if w != v} for v in vv}
        # Enumerate actual cycles as undirected edge sets.
        found = set()
        for a in vv:
            for b in adj[a]:
                for c in adj[b]-{a}:
                    for d in (adj[c] & adj[a])-{a,b,c}:
                        found.add(frozenset((edge(a,b),edge(b,c),edge(c,d),edge(d,a))))
        return len(found)
    previous = json.loads((ROOT/"frontier/experiments/i175_affected_prism_exterior/experiment-attempt-01.json").read_bytes())
    counts = [squares(es)]+[squares(list(map(tuple,r["graph"]["edges"]))) for r in previous["first_children"]]
    assert counts == [10,9,9]
    result = dict(status="PASS", complete_seven_family_records=2, complete_even_cut_sets=15,
                  surviving_states=11, survivor_products=46, matching_witnesses=900,
                  local_rank=5, exterior_rank=3, image_rank=9, extra_anchor_kernel=2,
                  survivor_rank=16, actual_survivor_minor_det="2", absorption_identities=3,
                  four_cycle_counts=counts, ambient_transport_rank=14,
                  helpers={str(p.relative_to(ROOT)):hashlib.sha256(p.read_bytes()).hexdigest()
                           for p in (HELPER,DET_HELPER)},
                  method="Parent-only DFS/path partitions, Fraction ranks and coordinate identities; no child code imported",
                  limits="No further surgery; historical control populations and U176 replay covered by sealed verifier. Four-cycle invariant suffices; no second isomorphism backtracking.")
    with (BASE.parent/"i177-parent-certificates.json").open("x") as out:
        json.dump(result,out,indent=2,sort_keys=True)
        out.write("\n")
    print("PASS: two seven-family records, 15 cut sets, 46 products, 900 matchings, two kernel corrections, three absorptions")


if __name__ == "__main__":
    main()
