"""Independent edge-level check of the 381292 family (Aharoni-Howard, arXiv:1605.06752 final Conjecture).

Sides M={m_1..m_n}, W={v_1..v_n} of K_{n,n}.  F_1 = {m_1 v_1}.  For 2<=i<=k,
F_i = {m_a v_1 : a<=n} u {m_a v_j : j>=2, a<=x_i}, x_2=2, x_i=2i-3 (i>=3).
(Every F_i is bipartitely shifted.)  a_ij = deg_{F_i}(v_j).
Checks: (H) sum_{i<=j} sorted r_i > j(j-1)n for all j<=k, and also the subset form
sum_{i in I}|F_i| > n|I|(|I|-1) for all nonempty I; (C) for EVERY pi in S_k, the
sorted sequence (a_{i,pi(i)}) violates sum_{i<=j} > j(j-1) for some j; also for every
injective map [k]->[n] (column choice beyond the first k).  Reports the best margin.
Also exhibits a rainbow matching (consistency with the source's Theorem).
usage: rainbow_certificate.py k n
"""
import sys, itertools, json

k, n = int(sys.argv[1]), int(sys.argv[2])
x = {2: 2}
for i in range(3, k + 1): x[i] = 2 * i - 3
F = {1: {(1, 1)}}
for i in range(2, k + 1):
    F[i] = {(a, 1) for a in range(1, n + 1)} | {(a, j) for j in range(2, n + 1) for a in range(1, x[i] + 1)}
for i in F:
    assert all(1 <= a <= n and 1 <= j <= n for a, j in F[i])
    # shiftedness: (a,j) in F, a'<=a, j'<=j  =>  (a',j') in F
    assert all((a2, j2) in F[i] for a, j in F[i] for a2 in range(1, a + 1) for j2 in range(1, j + 1))
A = {(i, j): sum(1 for a in range(1, n + 1) if (a, j) in F[i]) for i in F for j in range(1, n + 1)}
r = {i: len(F[i]) for i in F}
assert all(r[i] == sum(A[i, j] for j in range(1, n + 1)) for i in F)
rs = sorted(r.values())
H_sorted = all(sum(rs[:j]) > j * (j - 1) * n for j in range(1, k + 1))
H_subsets = all(sum(r[i] for i in I) > n * len(I) * (len(I) - 1)
                for t in range(1, k + 1) for I in itertools.combinations(range(1, k + 1), t))

def marg(vals):
    b = sorted(vals); s = 0; m = None
    for j in range(1, k + 1):
        s += b[j - 1]; v = s - j * (j - 1); m = v if m is None else min(m, v)
    return m
best_perm = max(marg([A[i, p[i - 1]] for i in range(1, k + 1)]) for p in itertools.permutations(range(1, k + 1)))
best_inj = max(marg([A[i, p[i - 1]] for i in range(1, k + 1)]) for p in itertools.permutations(range(1, n + 1), k))
# relaxed reading: all selected entries >= 1 and sum_{i<=j} sorted >= j(j-1) (non-strict) for j>=2
def relaxed_ok(vals):
    b = sorted(vals)
    if b[0] < 1: return False
    return all(sum(b[:j]) >= j * (j - 1) for j in range(2, k + 1))
relaxed = any(relaxed_ok([A[i, p[i - 1]] for i in range(1, k + 1)]) for p in itertools.permutations(range(1, k + 1)))
pos_margins = [marg(v) for v in ([A[i, p[i - 1]] for i in range(1, k + 1)] for p in itertools.permutations(range(1, k + 1))) if min(v) >= 1]
best_pos = max(pos_margins) if pos_margins else None
# weaker printed Theorem: some pi with sorted a_{i pi(i)} >= (1..k)
thm = any(all(b >= t for b, t in zip(sorted(A[i, p[i - 1]] for i in range(1, k + 1)), range(1, k + 1)))
          for p in itertools.permutations(range(1, k + 1)))
match = [(1, 1)] + [(i, i) for i in range(2, k + 1)]
rainbow = all(match[i - 1] in F[i] for i in range(1, k + 1)) and len({a for a, _ in match}) == k == len({j for _, j in match})
out = dict(k=k, n=n, row_sums=r, degree_rows={i: [A[i, j] for j in range(1, n + 1)] for i in F},
           hypothesis_sorted=H_sorted, hypothesis_all_subsets=H_subsets,
           best_margin_over_Sk=best_perm, best_margin_over_injections_into_n=best_inj,
           conjecture_conclusion_holds=best_perm >= 1,
           best_margin_over_positive_selections=best_pos, relaxed_nonstrict_conclusion_holds=relaxed, source_theorem_conclusion_holds=thm,
           rainbow_matching_exists=rainbow)
print(json.dumps(out))
