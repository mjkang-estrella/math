# PROOF: refutation of Defant–Propp Conjecture 4.4 (MathDB 345545)

DRAFT. This is an AI-assisted ordinary proof written for root review. It earns zero accepted credit; the root decides. The paper (`paper.pdf`, source `paper-src/paper.src.md` and `paper.md`) contains the same argument with source quotations, tables and the formal correspondence.

## Statement

Source: C. Defant and J. Propp, arXiv:2002.07144 v3/v4, Conjecture 4.4; Electron. J. Combin. 27(3) (2020) #P3.51, Conjecture 23. The conjecture reads: "The value of the limit lim_{n→∞} deg(s : S_n → S_n)^{1/n} lies in the interval (1.68, 1.73)." Here deg(f) = |X|^{-1} Σ_x |f^{-1}(f(x))| (Definition 1.1) and s is West's stack-sorting map, s(LmR) = s(L)s(R)m.

Notation: P_n = #{(σ, τ) ∈ S_n × S_n : s(σ) = s(τ)} and d_n = deg(s : S_n → S_n) = P_n / n!.

**Theorem 1.1.** For every k ≥ 0 and a_k = 131·2^k − 1, d_{a_k} > 1.73^{a_k}. Hence d_n^{1/n} > 1.73 infinitely often, every limit L satisfies L ≥ 1.73, and the conjecture is false. This theorem is formalised in Lean.

**Theorem 1.2.** lim d_n^{1/n} ≥ 1.80468, using the existence of the limit from the source's Theorem 2.5 and the exact P_82. This is not formalised.

*Correction to the brief:* the brief's figure "≥ 1.8047" is too strong. The exact bound is β_82 = 1.8046832…, and the integer test at 1.8047 fails (`evidence/math-check.json`: `exact_a82_bound_gt_1_8047 = false`, `exact_a82_bound_gt_1_80468 = true`).

## 1. Standardisation and the tree readout

L1. If φ is strictly increasing on the letters of w, then s(φ w) = φ(s w), by induction on |w|. Hence any k-letter alphabet has P_k colliding word pairs.

L2. Let T(w) be the decreasing binary tree of w, with root max w, left subtree T(L) and right subtree T(R). Its in-order reading is w and its postorder reading is s(w). Consequences: s(w) is a rearrangement of w; max w is the last letter of s(w); and the root has 0, 1 (left or right) or 2 children.

## 2. The top-max recursion

An r-tuple on [M] is a sequence of r nonempty words whose concatenation is a permutation of [M]. Its output is out(F) = s(F_1)⋯s(F_r). Its internal boundaries are β(F) = the partial sums |F_1|, …, |F_1| + ⋯ + |F_{r−1}|; these are also block ends in the output. We count:

- X(M,r,s): collisions, that is, pairs with out(F) = out(G);
- I(M,r,s): irreducible collisions, those with β(F) ∩ β(G) = ∅;
- Φ(M,r,s): maximum-final collisions, those whose output ends with M.

The base values are X(0,0,0) = 1, X(0,·,·) = 0 otherwise, and I(0,·,·) = 0. A single word has no internal boundary, so X(M,1,1) = I(M,1,1) = P_M.

T1 (common cut).

    X(M,r,s) = I(M,r,s) + Σ_{b=1}^{M−1} C(M,b) Σ_{a=1}^{r−1} Σ_{c=1}^{s−1} X(M−b,r−a,s−c) I(b,a,c).

Cut a reducible collision at its LAST common boundary p. The suffix pair is an irreducible collision, because a common internal boundary of it would be a later common boundary of the whole pair. Both suffixes have the same letter set A, namely the letters in the last M − p output positions, by L2. The prefix pair is an arbitrary collision on the complement of A. Conversely, gluing such a prefix pair to such a suffix pair gives a collision whose last common boundary is M − b. Counting with L1 gives C(M,b) X I.

T2 (maximum last). In an irreducible collision, M is the last output letter and lies in the last word of both tuples. M ends the sorted block containing it, so its output position p is a boundary in both tuples. If p < M, then p would be a common internal boundary.

T3 (deletion).

    Φ(M,r,s) = Σ_{t,u ∈ {0,1,2}} μ(t) μ(u) X(M−1, r−1+t, s−1+u),   with μ = (1, 2, 1).

Write the last word as A M B. Then s(A M B) = s(A) s(B) M. Replace the last word by the nonempty words among A and B; there are t of them. This gives an (r−1+t)-tuple on [M−1] whose output is the original output with the final M removed. The inverse takes the last t words as the children, of type leaf, left child, right child or two children. The number of types with t children is μ(t).

T4 (fixed maximum).

    Φ(M,r,s) = I(M,r,s) + Σ_b C(M−1,b−1) Σ_{a,c} X(M−b,r−a,s−c) I(b,a,c).

Irreducible collisions are maximum-final by T2. A reducible collision is maximum-final if and only if its T1 suffix letter set contains M, because by T2 the suffix output ends with the maximum of its own letters.

Theorem 4.5. Combining T3 and T4 gives I. Then T1 gives X. All terms on the right involve sizes smaller than M, and P_n = X(n,1,1). For P_N it suffices to take arities r, s ≤ min(M, N+1−M). The cost is O(N^6) arithmetic operations, which is polynomial.

## 3. Lower bounds

L3 (doubling, source inequality (1) with m = n = a+1): C(2a,a) P_a^2 ≤ P_{2a+1}, equivalently d_a^2 ≤ (2a+1) d_{2a+1}.

L4 (series-free iteration). Suppose 4(a+1)c ≤ d_a with c ≥ 0. Put a_0 = a and a_{k+1} = 2a_k + 1. Then d_{a_k} ≥ 4(a_k+1) c^{2^k}. For the inductive step,

    d_{a_{k+1}} ≥ d_{a_k}^2/(2a_k+1) ≥ 16(a_k+1)^2 c^{2^{k+1}}/(2a_k+1) ≥ 8(a_k+1) c^{2^{k+1}}.

Corollary: with β = (d_a/(4(a+1)))^{1/(a+1)} > 1, we get d_{a_k}^{1/a_k} > β for all k. This uses no logarithms, no series and no existence of the limit.

L5 (root split). For n ≥ 2,

    P_n ≥ 4 P_{n−1} + Σ_{i=1}^{n−2} C(n−1,i) P_i P_{n−1−i}.

The pairs (L n R, L′ n R′) with |L| = |L′| = i, s(L) = s(L′) and s(R) = s(R′) give C(n−1,i) P_i P_{n−1−i} pairs for i = 0, …, n−1. The cross pairs (n R, L′ n) and (L n, n R′) give 2P_{n−1} more. The families are disjoint, as the positions of n show.

L6 (certificate). Let G_n = P_n for n ≤ 20 and G_n = 4G_{n−1} + Σ C(n−1,i) G_i G_{n−1−i} for n > 20. By strong induction, G_n ≤ P_n. G_130 is the 254-digit literal `lower130`, and

    4·131·130!·173^131 < G_130·100^131.

## 4. Wrap-up

d_130 > 4·131·1.73^131. Apply L4 with a = 130 and c = 1.73^131. Then d_{a_k} ≥ 4(a_k+1)·1.73^{a_k+1} > 1.73^{a_k} for a_k = 131·2^k − 1.

Non-vacuity: d_n^{1/n} > 1.73 at n = 130, 261, 523, 1047, …. So the refutation does not rely on the limit failing to exist. If the limit L exists, then L ≥ 1.73, so L ∉ (1.68, 1.73).

With the exact P_82: β_82 = 1.8046832… > 1.80468, and with existence (source Theorem 2.5) L ≥ 1.80468. The same test passes at threshold 1.8 for a = 79, …, 82, which refutes the v1/v2 remark "(1.6, 1.8)". The numerical value of the limit is about 1.95 (heuristic only): d_82^{1/82} = 1.95107, d_82/d_81 = 1.95411, and a three-point fit gives 1.9532.

## 5. The reviewer's observation

The seeds P_1..P_13 alone, which are within brute-force range, together with L5 already pass the 1.73 test at a = 910 (seed depths 14, 16 and 20 give a = 446, 230 and 130; checked in `evidence/math-check.json`). This lowers the depth of the bare refutation. The recursion, the table up to 82, the bound 1.80468 and the estimate of about 1.95 are additions beyond it.

## 6. The MathDB paraphrase (no credit)

Read as "maximum fibre size", the statement is trivially false. F_n = {n p, p n : p ∈ F_{n−1}} has 2^{n−1} elements, all sorting to the identity. So the maximum fibre's n-th root is at least 2^{4/5} > 1.741 for n ≥ 5, and any limit is at least 2; the true limit is 4.

## 7. Diagnostics (not proof)

`scripts/check_math.py` (log in `logs/check-math-N82.*`) independently checks:

- brute-force P_1..P_8;
- T1–T4 literally on all tuple pairs with M ≤ 6;
- P_1..P_82 by the recursion, against the frozen table;
- L5 for n ≤ 82 and L3 for 2a+1 ≤ 81;
- G_130 = `lower130` and G_129 = `lower129`;
- the certificate and the controls at base 129 and threshold 1.95;
- seed-depth thresholds, and the exact a = 82 bounds.
