"""381292 (Aharoni-Howard arXiv:1605.06752, final Conjecture), shifted setting.

F_1..F_k bipartitely shifted subgraphs of K_{n,n}: the degree row (a_i1..a_in) of
F_i on side W is any nonincreasing sequence with entries in [0,n] (Ferrers graph).
Hypothesis: sorted row sums r satisfy sum_{i<=j} r_(i) > j(j-1)n for all j<=k.
Conclusion: some pi in S_k with sorted (a_{i,pi(i)}) having prefix sums > j(j-1).

Only the first k columns enter the conclusion; the hypothesis is monotone in the
row sums, so for given first-k entries c_1>=...>=c_k the row sum may be taken
maximal: R = sum c + (n-k) c_k.  Exhaustive over multisets of such k-rows.
usage: rainbow_search.py k n [also_literal]
"""
import sys, itertools, json

k, n = int(sys.argv[1]), int(sys.argv[2])
rows = []
def gen(prefix, hi):
    if len(prefix) == k:
        rows.append(tuple(prefix)); return
    for v in range(hi, -1, -1):
        gen(prefix + [v], v)
gen([], n)
R = {r: sum(r) + (n - k) * r[-1] for r in rows}
rows.sort(key=lambda r: R[r])
perms = list(itertools.permutations(range(k)))

def margin(M):
    """max over pi of min_j (prefix_j(sorted b) - j(j-1)); conjecture needs >= 1."""
    best = None
    for p in perms:
        b = sorted(M[i][p[i]] for i in range(k))
        s = 0; m = None
        for j in range(1, k + 1):
            s += b[j - 1]
            v = s - j * (j - 1)
            m = v if m is None else min(m, v)
        best = m if best is None else max(best, m)
    return best

count = 0; bad = []; worst = [None, None]
def rec(start, chosen, psum):
    global count
    j = len(chosen)
    if j == k:
        count += 1
        m = margin(chosen)
        if m <= 0 and len(bad) < 5:
            bad.append([list(r) for r in chosen])
        if worst[0] is None or m < worst[0]:
            worst[0] = m; worst[1] = [list(r) for r in chosen]
        return
    for idx in range(start, len(rows)):
        r = rows[idx]
        s = psum + R[r]
        if s <= (j + 1) * j * n:
            continue  # rows sorted by R: later rows have larger R, keep scanning
        rec(idx, chosen + [r], s)
rec(0, [], 0)
print(json.dumps({'k': k, 'n': n, 'rows': len(rows), 'hyp_satisfying_multisets': count,
                  'counterexamples_first5': bad[:5],
                  'min_margin': worst[0], 'min_margin_example': worst[1]}))
