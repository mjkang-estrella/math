"""Independent exact checks for MathDB 355701 (own code, not shared with author lane or r1).
(a) the claimed 9_3 counterexample; (b) all labeled 9_3 configurations (iso classes via aut order);
(c) inclusion-reading triviality: Fano + Pappus disjoint union and the source's own Fano connected sum.
Usage: python3 -I v3_verify.py OUT.json"""
import json, sys, time, itertools
t0 = time.time()
def analyse(lines, npts, want_aut=False):
    L = [frozenset(l) for l in lines]; m = len(L)
    ax = {"n_points": npts, "n_lines": m, "line_sizes_ok": all(len(l) == 3 for l in L),
          "point_degrees_ok": all(sum(pt in l for l in L) == 3 for pt in range(npts)),
          "pairs_on_at_most_one_line": all(len(a & b) <= 1 for a, b in itertools.combinations(L, 2)), "distinct_lines": len(set(L)) == m}
    meet = [[i != j and bool(L[i] & L[j]) for j in range(m)] for i in range(m)]
    # triangles (source Def. 4.1): three lines pairwise meeting in three distinct points (=> non-concurrent)
    tris = [ (i, j, k) for i, j, k in itertools.combinations(range(m), 3)
             if meet[i][j] and meet[i][k] and meet[j][k] and len((L[i] & L[j]) | (L[i] & L[k]) | (L[j] & L[k])) == 3]
    # cross-check with point-based definition
    ptris = set()
    for a, b, c in itertools.combinations(range(npts), 3):
        def line(u, v): 
            s = [i for i in range(m) if u in L[i] and v in L[i]]; return s[0] if s else None
        l1, l2, l3 = line(a, b), line(b, c), line(a, c)
        if None not in (l1, l2, l3) and c not in L[l1] and a not in L[l2] and b not in L[l3]: ptris.add(tuple(sorted((l1, l2, l3))))
    tmask = [(1 << i) | (1 << j) | (1 << k) for i, j, k in tris]
    best = min(sum(1 for t in tmask if (c & t) == t or (c & t) == 0) for c in range(1 << m))
    # intersecting families
    inter = [s for s in range(1 << m) if all(meet[i][j] for i in range(m) for j in range(i + 1, m) if s >> i & 1 and s >> j & 1)]
    iset = set(inter); omega = max(bin(s).count("1") for s in inter)
    incl_max = sorted({bin(s).count("1") for s in inter if s and all((s | 1 << j) not in iset for j in range(m) if not s >> j & 1)})
    out = dict(ax, n_triangles=len(tris), triangles_match_point_def=set(tris) == ptris, min_mono=best,
               max_intersecting=omega, inclusion_maximal_sizes=incl_max)
    if want_aut:
        LS = set(L); out["aut_order"] = sum(1 for perm in itertools.permutations(range(npts)) if all(frozenset(perm[x] for x in l) in LS for l in L))
    return out
res = {}
CEX = [{0,2,3},{2,4,5},{3,5,8},{2,7,8},{1,3,6},{0,6,8},{0,1,4},{4,6,7},{1,5,7}]
res["counterexample"] = analyse(CEX, 9, want_aut=True)
S = [CEX[i] for i in range(4)]
res["counterexample"]["lines_0_3_pairwise_meet"] = all(a & b for a, b in itertools.combinations(S, 2))
# (b) all labeled 9_3 configurations: lines through point 0 fixed as {0,1,2},{0,3,4},{0,5,6} is NOT WLOG for labeled counts,
# so enumerate all labeled ones by backtracking over the 84 triples.
triples = [frozenset(t) for t in itertools.combinations(range(9), 3)]
classes = {}; total = 0
def rec(start, chosen, deg, pairs):
    global total
    if len(chosen) == 9:
        total += 1
        key = None
        a = analyse(chosen, 9); key = (a["n_triangles"], a["max_intersecting"], a["min_mono"])
        c = classes.setdefault(key, {"count": 0, "example": [sorted(l) for l in chosen]}); c["count"] += 1
        return
    # the smallest point with degree < 3 must be covered by the next line (canonical order)
    pt = min(x for x in range(9) if deg[x] < 3)
    for idx in range(start, len(triples)):
        t = triples[idx]
        if pt not in t or min(t) != pt: continue
        if any(deg[x] >= 3 for x in t): continue
        pr = {frozenset(e) for e in itertools.combinations(t, 2)}
        if pr & pairs: continue
        for x in t: deg[x] += 1
        rec(idx + 1, chosen + [t], deg, pairs | pr)
        for x in t: deg[x] -= 1
rec(0, [], [0] * 9, frozenset())
res["all_labeled_9_3"] = {"total_labeled": total, "expected_9!/108+9!/9+9!/12": 362880 // 108 + 362880 // 9 + 362880 // 12,
                          "classes_(n_triangles,max_intersecting,min_mono)": {str(k): v for k, v in classes.items()}}
# (c) inclusion-reading triviality
FANO = [{0,1,2},{0,3,4},{0,5,6},{1,3,5},{1,4,6},{2,3,6},{2,4,5}]
PAPPUS = [{0,1,2},{3,4,5},{6,7,8},{0,4,8},{0,5,7},{1,3,8},{1,5,6},{2,3,7},{2,4,6}]
res["fano"] = analyse(FANO, 7); res["pappus"] = analyse(PAPPUS, 9)
res["fano_disjoint_union_pappus"] = analyse(FANO + [{x + 7 for x in l} for l in PAPPUS], 16)
# connected sum (source Sec. 5): Fano A on 0..6, Fano B on 7..13; p1=0 on l1={0,1,2} in A, p2=7 on l2={7,8,9} in B; swap.
A = [set(l) for l in FANO]; B = [{x + 7 for x in l} for l in FANO]
A[0] = {7, 1, 2}; B[0] = {0, 8, 9}
res["fano_connected_sum"] = analyse(A + B, 14)
res["seconds"] = round(time.time() - t0, 2)
json.dump(res, open(sys.argv[1], "w"), indent=1); print(json.dumps(res, indent=1))
