"""Reviewer's solver-logic controls: generic (p,q) existence by exhaustive p, decoupled q."""
import itertools, json, sys
def blocker(E, V):
    tr = [frozenset(T) for k in range(len(V)+1) for T in itertools.combinations(V, k) if all(set(e) & set(T) for e in E)]
    s = set(tr); return [T for T in tr if not any(T - {v} in s for v in T)]
def has_pq(E, V):
    E = [sorted(e) for e in E]; B = blocker(E, V)
    single = [[(i, next(iter(set(E[i]) & T))) for i in range(len(E)) if len(set(E[i]) & T) == 1] for T in B]
    for ch in itertools.product(*[range(len(e)) for e in E]):
        p = [E[i][ch[i]] for i in range(len(E))]
        if all(not ({v for i, v in single[j] if p[i] == v} >= T) for j, T in enumerate(B)):
            return True, len(B)
    return False, len(B)
cases = {
 "cyclic_C11_3 (Pap Thm3.4.9: expect True)": ([{i,(i+1)%11,(i+2)%11} for i in range(11)], range(11)),
 "odd_hole_C5_2 (mni, cyclic: expect True)": ([{i,(i+1)%5} for i in range(5)], range(5)),
 "Fano F7 (mni, cyclic core: expect True)": ([{i,(i+1)%7,(i+3)%7} for i in range(7)], range(7)),
 "J3 degenerate plane (expect True per author/Pap reduction)": ([{1,2,3},{0,1},{0,2},{0,3}], range(4)),
 "path 01,12 (ideal: expect False)": ([{0,1},{1,2}], range(3)),
 "C4 edges (bipartite, ideal: expect False)": ([{i,(i+1)%4} for i in range(4)], range(4)),
 "C6 edges (bipartite, ideal: expect False)": ([{i,(i+1)%6} for i in range(6)], range(6)),
 "C11 candidate (expect False)": ([{1,7,10},{2,3,8},{2,3,4},{0,3,4},{0,1,4},{0,5,6},{5,6,7},{1,6,7},{2,8,9},{8,9,10},{5,9,10}], range(11)),
}
res = {k: dict(zip(["has_pq","blocker_size"], has_pq(E, list(V)))) for k, (E, V) in cases.items()}
json.dump(res, sys.stdout, indent=1); print()
