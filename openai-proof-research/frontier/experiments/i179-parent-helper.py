"""Bounded follow-up: actual same-type helpers for the retained locked P path."""
import json
import runpy
from itertools import combinations
from pathlib import Path

ROOT = Path(__file__).resolve().parents[2]
HERE = ROOT/"frontier/experiments"
H = runpy.run_path(str(HERE/"i175-parent-certificates.py"))


def main():
    record = json.loads((HERE/"i179_path_recombination/analytic-attempt-03.json").read_bytes())["systems"][0]
    es = tuple(map(tuple,record["local_edges"]))
    vertices = tuple(sorted({v for e in es for v in e}))
    boundary = record["boundary"]
    p = sorted(H["packings"](es,vertices,((13,19),)))
    fibres = []
    for state in record["states"]:
        pairs = tuple((boundary[a],boundary[b]) for a,b in state["px"])
        fresh = sorted(H["packings"](es,vertices,pairs))
        assert fresh == list(map(tuple,state["X"]))
        fibres.append(fresh)
    assert len(p) == 5 and len(fibres) == 11 and len(fibres[0]) == 1
    solutions = []
    for j in range(1,len(p)):
        for state,fibre in enumerate(fibres):
            for i,u in enumerate(fibre):
                for k,v in enumerate(fibre):
                    assert len(u) == len(v) == len(p[0])
                    if all(a+b == c+d for a,b,c,d in zip(p[0],u,p[j],v)):
                        changed = [es[q] for q in range(len(es)) if p[0][q] != p[j][q]]
                        # A single alternating cycle gives a completed,
                        # cycle-free two-colour move with the third helper idle.
                        adj = {}
                        for a,b in changed:
                            adj.setdefault(a,set()).add(b)
                            adj.setdefault(b,set()).add(a)
                        seen,stack = set(),[min(adj)]
                        while stack:
                            a = stack.pop()
                            if a not in seen:
                                seen.add(a)
                                stack.extend(adj[a]-seen)
                        simple_cycle = seen == set(adj) and all(len(ns)==2 for ns in adj.values())
                        alternating = all(sum(p[0][es.index(tuple(sorted((a,b))))] for b in ns)==1
                                          for a,ns in adj.items())
                        solutions.append(dict(P_index=j,state=state,u_index=i,up_index=k,
                                              changed_edges=changed,single_alternating_cycle=simple_cycle and alternating))
    def words(vector):
        adj = {v:[] for v in vertices}
        for (a,b),used in zip(es,vector):
            if used:
                adj[a].append(b)
                adj[b].append(a)
        unseen,result = set(vertices),[]
        while unseen:
            ends = sorted(v for v in unseen if len(adj[v])==1)
            assert ends
            path,previous,current = [],None,ends[0]
            while True:
                path.append(current)
                unseen.remove(current)
                choices = [v for v in adj[current] if v != previous]
                if not choices:
                    break
                assert len(choices)==1
                previous,current = current,choices[0]
            result.append(path)
        return result
    direct = [z for z in solutions if z["single_alternating_cycle"]]
    witness = None
    if direct:
        z = direct[0]
        u,up = fibres[z["state"]][z["u_index"]],fibres[z["state"]][z["up_index"]]
        pp = p[z["P_index"]]
        s = fibres[0][0]
        assert all(a+b+c == d+e+f for a,b,c,d,e,f in zip(p[0],s,u,pp,s,up))
        witness = dict(**z,p=words(p[0]),s=words(s),u=words(u),pp=words(pp),up=words(up),
                       equation="p+s+u = pprime+s+uprime; s is unchanged throughout",
                       completed_exchanges=1)
    output = dict(status="PASS",scope="Fixed I177 graph, first locked P packing only; all actual same-survivor-type helper pairs",
                  new_graphs=0,solutions=solutions,single_cycle_solutions=len(direct),witness=witness,
                  limits="Finite helper check, not L179 or a general graph-independent recombination theorem.")
    with (HERE/"i179-parent-helper.json").open("x") as out:
        json.dump(output,out,indent=2,sort_keys=True)
        out.write("\n")
    print(json.dumps(output,indent=2))


if __name__ == "__main__":
    main()
