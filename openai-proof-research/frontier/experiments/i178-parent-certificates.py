"""Independent parent fixed-exterior exhaustion and exact relation checks."""
import hashlib
import json
import runpy
from fractions import Fraction as F
from itertools import combinations, product
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
BASE = ROOT / "frontier/experiments/i178_five_port_annihilator"
HELPER = BASE.parent / "i175-parent-certificates.py"
H = runpy.run_path(str(HELPER))
edge,packings,cycles,rank,differences,minus = (
    H[k] for k in ("edge","packings","cycles","rank","differences","minus"))
RELATIONS = [
    [0,0,0,1,-1,0,0,-1,1,0,0,0,0],
    [0,0,0,1,0,-1,0,-1,0,0,1,0,0],
    [0,0,0,-1,0,0,0,0,0,-1,0,1,0],
    [0,0,0,-1,0,0,-1,1,0,-1,0,0,1]]
PICKS = [0,1,2,3,4,5,6,7,9]


def read(rel):
    return json.loads((ROOT/rel).read_bytes())


def rows(value):
    return [tuple(map(F,r)) for r in value]


def combine(coeff,basis):
    assert len(coeff) == len(basis)
    return tuple(sum(F(a)*r[i] for a,r in zip(coeff,basis)) for i in range(len(basis[0])))


def nullspace(matrix,n):
    a = [list(map(F,r)) for r in matrix]
    pivots = []
    for j in range(n):
        i = len(pivots)
        p = next((p for p in range(i,len(a)) if a[p][j]),None)
        if p is None:
            continue
        a[i],a[p] = a[p],a[i]
        z = a[i][j]
        a[i] = [x/z for x in a[i]]
        for p in range(len(a)):
            if p != i:
                z = a[p][j]
                a[p] = [x-z*y for x,y in zip(a[p],a[i])]
        pivots.append(j)
    result = []
    for j in range(n):
        if j not in pivots:
            row = [F(0)]*n
            row[j] = F(1)
            for i,p in enumerate(pivots):
                row[p] = -a[i][j]
            result.append(tuple(row))
    return result


def possible_pairings(J):
    if len(J) == 2:
        return [((J[0],J[1]),)]
    return [tuple(sorted(((J[0],J[i]),tuple(v for v in J if v not in (J[0],J[i])))))
            for i in (1,2,3)]


def vec(es,chosen):
    return tuple(int(e in chosen) for e in es)


def main():
    analytic = read("frontier/experiments/i178_five_port_annihilator/analytic-attempt-05.json")
    new = read("frontier/experiments/i177_adjacent_port_surgery/experiment-attempt-03.json")["fiveport"]
    mandatory = read("frontier/experiments/i177_adjacent_port_surgery/mandatory-attempt-05.json")
    audit = read("frontier/experiments/i177_adjacent_port_surgery/audit-attempt-03.json")
    p8 = read("frontier/experiments/i175_affected_prism_exterior/experiment-attempt-01.json")
    second = dict(new,graph=p8["first_children"][1]["graph"])
    specs = [new,mandatory["first_P8_fiveport"],second,audit["k4"],
             mandatory["I176_k6"]["complete_fiveport"]]
    results, total_changes = [],0
    assert len(analytic["systems"]) == len(specs) == 5
    for record,spec in zip(analytic["systems"],specs):
        es = list(map(tuple,spec["graph"]["edges"]))
        X,Y = set(spec["X"]),set(spec["Y"])
        xe,ye = ([e for e in es if set(e) <= side] for side in (X,Y))
        cut = list(map(tuple,spec["cut"]))
        xp = [next(v for v in e if v in X) for e in cut]
        yp = [next(v for v in e if v in Y) for e in cut]
        pi = [i for i,e in enumerate(es) if e not in xe]
        xi = [es.index(e) for e in xe]
        def lift(x,y,J):
            return vec(es,{e for e,a in zip(xe,x) if a} |
                       {e for e,a in zip(ye,y) if a} | {cut[i] for i in J})
        states,full,kept,lost,WX,WY = [],set(),set(),[],[],[]
        abstract_survivor,abstract_lost = set(),set()
        families = []
        for size in (2,4):
            for J in combinations(range(5),size):
                groups = []
                for ee,side,end in ((xe,X,xp),(ye,Y,yp)):
                    grouped = {}
                    for pair in possible_pairings(J):
                        rr = sorted(packings(tuple(ee),tuple(sorted(side)),
                                             tuple((end[a],end[b]) for a,b in pair)))
                        if rr:
                            grouped[pair] = rr
                    groups.append(grouped)
                xx,yy = groups
                families.append((J,xx,yy))
                # Exhaust every noncrossing local pairing, even if absent in X.
                order = [0,2,1,4,3]
                for px in possible_pairings(J):
                    positions = [order.index(v) for v in J]
                    ordered = sorted(J,key=order.index)
                    crossing = size == 4 and {frozenset(p) for p in px} == {
                        frozenset((ordered[0],ordered[2])),frozenset((ordered[1],ordered[3]))}
                    if crossing:
                        continue
                    for py,yr in yy.items():
                        if size == 4 and px == py:
                            continue
                        for y in yr:
                            target = abstract_survivor if 2 in J or y[ye.index((1,7))] else abstract_lost
                            target.add((J,px,py))
                for px,xr in xx.items():
                    for py,yr in yy.items():
                        if size == 4 and px == py:
                            continue
                        allrows = {lift(x,y,J) for x,y in product(xr,yr)}
                        assert not full & allrows
                        full |= allrows
                        good = [y for y in yr if 2 in J or y[ye.index((1,7))]]
                        bad = [y for y in yr if 2 not in J and not y[ye.index((1,7))]]
                        if bad:
                            lost.append((J,px,py,xr,bad))
                        if good:
                            anchor = lift(xr[0],good[0],J)
                            states.append(dict(J=J,px=px,py=py,X=xr,Y=good,anchor=anchor))
                            kept |= {lift(x,y,J) for x,y in product(xr,good)}
                            WX += [minus(lift(x,good[0],J),anchor) for x in xr[1:]]
                            WY += [minus(lift(xr[0],y,J),anchor) for y in good[1:]]
        fresh_cycles = {vec(es,c) for c in cycles(es,X|Y)}
        assert full == fresh_cycles and len(full) == record["full_products"]
        assert kept == {c for c in full if c[es.index(cut[2])] or c[es.index((1,7))]}
        assert len(kept) == record["survivor_products"]
        assert len(abstract_survivor) == 11 and abstract_survivor == {
            (s["J"],s["px"],s["py"]) for s in states}
        assert {(J,px) for J,px,py in abstract_lost} == {
            ((0,1),((0,1),)),((0,1,3,4),((0,1),(3,4)))}
        anchors = [s["anchor"] for s in states]
        p = record["presentation"]
        assert anchors == rows(p["actual_anchors"])
        for s,t in zip(states,p["states"]):
            assert s["X"] == rows(t["X"]) and s["Y"] == rows(t["Y"])
        outer = rows(p["exterior_basis"])
        assert rank(outer) == rank(outer+WY) == 3
        generators = outer+differences(anchors)
        projected = [tuple(r[i] for i in pi) for r in generators]
        assert generators == rows(p["generators"]) and projected == rows(p["projected_generators"])
        relations = nullspace(list(zip(*projected)),13)
        assert relations == rows(RELATIONS) == rows(p["relation_basis"])
        K = [combine(r,generators) for r in relations]
        assert K == rows(p["actual_lifts"]) and all(not any(k[i] for i in pi) for k in K)
        assert rank([projected[i] for i in PICKS]) == 9
        a,kr = rank(WX),rank(WX+K)
        assert (a,kr-a,rank(differences(sorted(kept)))) == (p["a"],p["r"],9+kr)
        assert rank(WX+K+rows(p["kernel_basis"])) == rank(rows(p["kernel_basis"])) == kr
        if record["name"] == "I177":
            xb = rows(p["local_basis"])
            assert combine([3],[K[2]]) == combine([3],[K[3]]) == combine(
                [5,-1,-1,-1,-1,1,2],xb+K[:2])
        # Check all individual actual anchor changes, including changes of c0.
        changes = []
        for si,st in enumerate(states):
            changes += [(si,j,0) for j in range(1,len(st["X"]))]
            changes += [(si,0,j) for j in range(1,len(st["Y"]))]
        assert len(changes) == len(record["single_anchor_changes"])
        for choice,certificate in zip(changes,record["single_anchor_changes"]):
            assert tuple(certificate["actual_anchor_choice"]) == choice
            si,x,y = choice
            alt = anchors[:]
            alt[si] = lift(states[si]["X"][x],states[si]["Y"][y],states[si]["J"])
            gg = outer+differences(alt)
            rel = nullspace(list(zip(*(tuple(g[i] for i in pi) for g in gg))),13)
            kk = [combine(r,gg) for r in rel]
            assert rel == rows(certificate["relation_basis"]) and kk == rows(certificate["actual_lifts"])
            assert rank(WX+K+kk) == kr
            assert kk == [combine(c,rows(p["kernel_basis"]))
                          for c in certificate["lift_coordinates_in_original_kernel"]]
        total_changes += len(changes)
        cp = record["changed_anchors"]
        last = [lift(s["X"][-1],s["Y"][-1],s["J"]) for s in states]
        yalt = [combine([1,1],outer[:2]),outer[1],combine([-1],[outer[2]])]
        assert rows(cp["actual_anchors"]) == last
        assert rows(cp["generators"]) == yalt+differences(last)
        cg = rows(cp["generators"])
        cr = nullspace(list(zip(*(tuple(r[i] for i in pi) for r in cg))),13)
        ck = [combine(r,cg) for r in cr]
        assert cr == rows(cp["relation_basis"]) and ck == rows(cp["actual_lifts"])
        assert rank(WX+K+ck) == kr
        # Complete the full-cycle kernel using every actual lost packing.
        completion = record["completion_constraints"]
        assert len(lost) == len(completion["lost_types"]) == 2
        liftbasis = [generators[i] for i in PICKS]
        residuals = []
        for (J,px,py,xx,yy),t in zip(lost,completion["lost_types"]):
            assert (list(J),list(map(list,px)),list(map(list,py))) == (t["J"],t["px"],t["py"])
            assert xx == rows(t["local_fibre"]) and len(yy) == len(t["exterior_fibres"]) == 3
            target_coeff = [1,0,1,-1,4,-4,0,0,0,0,0] if len(J)==2 else [0,0,1,-1,4,-4,0,1,0,0,0]
            target = tuple(combine(target_coeff,anchors)[i] for i in xi)
            for index,(y,f) in enumerate(zip(yy,t["exterior_fibres"])):
                assert y == tuple(f["exterior"]) and target == tuple(map(F,f["local_target"]))
                coeff = [-3,1+int(index==1),1+int(index==2),0,1,-1,4,-4,int(len(J)==4)]
                assert tuple(map(F,f["image_coordinates"])) == tuple(coeff)
                for x,z in zip(xx,f["actual_local_residuals"]):
                    cycle = lift(x,y,J)
                    assert cycle in full-kept
                    actual = minus(minus(cycle,anchors[0]),combine(coeff,liftbasis))
                    assert all(actual[i] == 0 for i in pi)
                    assert tuple(actual[i] for i in xi) == minus(x,target) == tuple(map(F,z))
                    residuals.append(actual)
        local_inc = [tuple(int(v in e) for e in xe) for v in X]
        global_inc = [tuple(int(v in e) for e in es) for v in X|Y]
        h = len(xe)-rank(local_inc)
        assert rank(WX+K+residuals) == h == p["h"]
        assert rank(differences(sorted(full))) == len(es)-rank(global_inc) == h+9
        ann = rows(p["local_annihilators"])
        assert all(sum(w[i]*v[es.index(e)] for i,e in enumerate(xe)) == 0 for w in ann for v in WX+K)
        assert rank(ann) == len(xe)-kr and rank(ann+local_inc) == rank(ann)
        results.append(dict(name=record["name"],full=len(full),survivors=len(kept),h=h,
                            a=a,r=kr-a,image=9,loss=h-kr,anchor_changes=len(changes),
                            relations=4,lost_types=2,lost_products=len(full-kept)))
    assert total_changes == 84
    result = dict(status="PASS",systems=results,individual_anchor_changes=84,
                  abstract_fixed_exterior="All noncrossing local pairings exhausted: eleven survivor types and two lost types",
                  method="Parent DFS/path partitions and independent Fraction nullspaces; all actual completion and anchor-change identities",
                  helper=str(HELPER.relative_to(ROOT)),helper_sha256=hashlib.sha256(HELPER.read_bytes()).hexdigest(),
                  limits="Only five retained systems. No nonzero annihilator realization, general path-recombination theorem or new graph.")
    with (BASE.parent/"i178-parent-certificates.json").open("x") as out:
        json.dump(result,out,indent=2,sort_keys=True)
        out.write("\n")
    print("PASS: five full products, four relations, 84 anchor changes, two complete lost types and residual formulas")


if __name__ == "__main__":
    main()
