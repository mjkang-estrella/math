"""Independent parent DFS and complete helper-move checks for I180."""
import hashlib
import json
import runpy
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT/"frontier/experiments"
BASE = HERE/"i180_survivor_helper_connectivity"
HELPER = HERE/"i175-parent-certificates.py"
H = runpy.run_path(str(HELPER))


def main():
    data = json.loads((BASE/"calibration-attempt-02.json").read_bytes())
    old = json.loads((HERE/"i177_adjacent_port_surgery/experiment-attempt-03.json").read_bytes())["fiveport"]
    states = json.loads((HERE/"i179_path_recombination/analytic-attempt-03.json").read_bytes())["systems"][0]["states"]
    es = tuple(map(tuple,old["xe"]))
    vertices = tuple(sorted({v for e in es for v in e}))
    boundary = (13,19,20,30,31)
    P = sorted(H["packings"](es,vertices,((13,19),)))
    fibres = [sorted(H["packings"](es,vertices,tuple((boundary[a],boundary[b]) for a,b in st["px"])))
              for st in states]
    assert len(P) == 5 and [len(f) for f in fibres] == [1,2,1,1,2,5,5,1,1,5,2]
    assert P == [tuple(p["vector"]) for p in data["P"]]
    assert all(f == list(map(tuple,st["X"])) for f,st in zip(fibres,states))

    def components(indices):
        adj = {}
        for i in indices:
            a,b = es[i]
            adj.setdefault(a,set()).add(b)
            adj.setdefault(b,set()).add(a)
        unseen,result = set(adj),[]
        while unseen:
            stack,seen = [min(unseen)],set()
            while stack:
                v = stack.pop()
                if v not in seen:
                    seen.add(v)
                    stack.extend(adj[v]-seen)
            unseen -= seen
            result.append((seen,tuple(i for i in indices if es[i][0] in seen)))
        return adj,result

    def described(info):
        chosen,used,pairs = set(),[],[]
        for closed,key in ((False,"paths"),(True,"cycles")):
            for w in info[key]:
                assert len(w) >= 2
                core = w[:-1] if closed else w
                assert len(core) == len(set(core))
                if closed:
                    assert w[0] == w[-1]
                else:
                    pairs.append(tuple(sorted((w[0],w[-1]))))
                used += core
                for a,b in zip(w,w[1:]):
                    e = tuple(sorted((a,b)))
                    assert e in es and e not in chosen
                    chosen.add(e)
        assert sorted(used) == list(vertices)
        assert sorted(pairs) == list(map(tuple,info["pairing"]))
        return tuple(int(e in chosen) for e in es)

    for p,entry in zip(P,data["P"]):
        assert described(dict(paths=entry["paths"],cycles=[],pairing=[(13,19)])) == p
    candidates,successful = {},set()
    for a,p in enumerate(P):
        for si,fibre in enumerate(fibres):
            for b,u in enumerate(fibre):
                diff = tuple(i for i in range(len(es)) if p[i] != u[i])
                adj,cc = components(diff)
                for vs,ids in cc:
                    if not all(len(adj[v]) == 2 for v in vs):
                        continue
                    q = tuple(u[i] if i in ids else p[i] for i in range(len(es)))
                    v = tuple(p[i] if i in ids else u[i] for i in range(len(es)))
                    key = (a,si,b,ids)
                    valid = q in P and v in fibre
                    candidates[key] = (q,v,valid)
                    if valid:
                        successful.add((a,P.index(q),si,b,fibre.index(v)))
    covered = set()
    for record in data["witnesses"]+data["rejected_cycle_moves"]:
        key = (record["p_index"],record["state"],record["u_index"],
               tuple(es.index(tuple(e)) for e in record["cycle_edges"]))
        assert key not in covered
        covered.add(key)
        q,v,valid = candidates[key]
        assert described(record["q"]) == q and described(record["v"]) == v
        assert record["valid"] == valid
        if valid:
            assert described(record["p"]) == P[key[0]]
            assert described(record["u"]) == fibres[key[1]][key[2]]
            assert not record["q"]["cycles"] and not record["v"]["cycles"]
            assert (key[0],record["q_index"],key[1],key[2],record["v_index"]) in successful
        else:
            assert record["q"]["cycles"],"Every rejected move must obstruct the lost path"
    assert covered == set(candidates) and len(candidates) == 123
    assert len(successful) == len(data["witnesses"]) == 24
    assert len(data["rejected_cycle_moves"]) == 99
    # Separately exhaust all exact sum identities and test their whole-cycle geometry.
    identities = set()
    for a,c in combinations(range(5),2):
        changed = tuple(i for i in range(len(es)) if P[a][i] != P[c][i])
        adj,cc = components(changed)
        if len(cc) != 1 or any(len(ns) != 2 for ns in adj.values()):
            continue
        for si,fibre in enumerate(fibres):
            for b,u in enumerate(fibre):
                for d,v in enumerate(fibre):
                    if all(p+x == q+y for p,x,q,y in zip(P[a],u,P[c],v)):
                        assert not any(P[a][i] != u[i] and i not in changed and set(e)&set(adj)
                                       for i,e in enumerate(es))
                        identities.add((a,c,si,b,d))
    assert identities == {s for s in successful if s[0]<s[1]} == set(map(tuple,data["independent_identity_enumeration"]))
    edges = sorted({tuple(sorted((a,c))) for a,c,si,b,d in successful})
    assert edges == [(0,1),(1,2),(2,3),(3,4)] == list(map(tuple,data["edges"]))
    assert data["components"] == [[0,1,2,3,4]] and data["connected"]
    distances = [[sum(a!=b for a,b in zip(p,q)) for q in P] for p in P]
    assert distances == data["hamming_distance"]
    assert [distances[i][4] for i in range(5)] == [8,8,8,6,0]
    assert not any(distances[c][4] < distances[0][4] for a,c in edges if a == 0)
    for item in data["nine_parent_identities_fixed_pair_lock"]:
        si,j = item["state"],item["P_index"]
        assert si in (5,6,9) and j in (2,3,4)
        assert all(a+b==c+d for a,b,c,d in zip(P[0],fibres[si][j],P[j],fibres[si][0]))
        assert not any(a == 0 and state == si and b == j for a,c,state,b,d in successful)
    assert len(data["nine_parent_identities_fixed_pair_lock"]) == 9
    WX = [d for f in fibres for d in H["differences"](f)]
    PD = H["differences"](P)
    assert H["rank"](WX) == H["rank"](WX+PD) == data["WX_rank"] == 5
    assert H["rank"](PD) == data["P_difference_rank"] == 4
    assert data["weaker_containment"]
    result = dict(status="PASS",complete_P=5,survivor_packings=sum(map(len,fibres)),
                  overlays=130,cycle_moves=123,directed_witnesses=24,rejected_with_lost_cycles=99,
                  helper_edges=edges,independent_forward_identities=len(identities),
                  fixed_pair_locks=9,target4_hamming_distances=[8,8,8,6,0],
                  ranks=dict(P=4,WX=5,combined=5),
                  method="Committed parent DFS/path partitions plus fresh component, exact-sum, word and Fraction-rank checks",
                  helper=str(HELPER.relative_to(ROOT)),helper_sha256=hashlib.sha256(HELPER.read_bytes()).hexdigest(),
                  limits="One retained graph. Inherited controls, matching certificates and full presentations replayed, not independently rescanned. No universal result.")
    with (HERE/"i180-parent-certificates.json").open("x") as out:
        json.dump(result,out,indent=2,sort_keys=True)
        out.write("\n")
    print("PASS: complete helper path, 24 witnesses, 99 rejected moves, nine fixed-pair locks and Hamming plateau")


if __name__ == "__main__":
    main()
