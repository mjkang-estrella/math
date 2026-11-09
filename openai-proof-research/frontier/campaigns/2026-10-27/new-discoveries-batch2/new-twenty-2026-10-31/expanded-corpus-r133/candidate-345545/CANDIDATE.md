# Candidate 345545: refutation of the Defant–Propp stack-sorting degree conjecture

Status: candidate for root review. Not self-accepted. No Lean was run in this lane (memory restriction). The Lean draft in `lean/` is UNCOMPILED and incomplete; see "Lean plan" below.

## 1. Exact source statement and scope

Source: C. Defant and J. Propp, "Quantifying Noninvertibility in Discrete Dynamical Systems", arXiv:2002.07144. Versions v1 (2020-02-17), v2 (2020-02-18), v3 (2020-03-29) and v4 (2020-09-27); published in Electron. J. Combin. 27(3) (2020). v4 was read (`downloads/2002.07144v4`, sha256 in its receipt).

- Definition 1.1 (v4): for f : X → Y, deg(f) = (1/|X|) Σ_{x∈X} |f⁻¹(f(x))| = (1/|X|) Σ_{y∈Y} |f⁻¹(y)|².
- Section 2.3: s is West's stack-sorting map, s(LmR) = s(L)s(R)m.
- Theorem 2.5: lim_{n→∞} deg(s : S_n → S_n)^{1/n} exists and lies in [1.12462, 4]. The proof shows d_{m−1}d_{n−1} ≤ (m+n−1)d_{m+n−1} (inequality (1)) and lim d_n^{1/n} = sup_{n≥8} (d_{n−1}/n²)^{1/n}.
- Conjecture 4.4 (v4, Section 4): "The value of the limit lim_{n→∞} deg(s : S_n → S_n)^{1/n} lies in the interval (1.68, 1.73)." The evidence was the mean of |s⁻¹(s(π))|^{1/n} over random π for n = 100 and n = 300 (1.69 and 1.70).

MathDB record 345545 paraphrases deg as "maximum fiber size". That is a paraphrase defect. The maximum fiber is |s⁻¹(id)| = C_n, whose n-th root tends to 4, so the literal record is refuted trivially; that version receives no credit. This candidate addresses the SOURCE quantity, the average multiplicity.

Later literature: C. Defant, "Troupes, Cumulants, and Stack-Sorting", arXiv:2004.11367v2 (2022-01-10), Theorem 7.29, proves lim > 1.62924. It restates the conjecture (1.68, 1.73) as open, and Remark 7.30 says brute force cannot go beyond about n = 14. Nothing later was found (bounded web search; see SUMMARY receipts).

## 2. Result

Theorem. Let d_n = deg(s : S_n → S_n). Then lim_{n→∞} d_n^{1/n} > 1.733. In particular Conjecture 4.4 is false. Numerically the limit is about 1.953 (extrapolation; heuristic only).

The certificate is the exact integer P_50 = 50!·d_50, together with P_50·100^51 > 4·51·50!·173^51 (checked exactly in `scripts/stack_certificate.py`; the values are in `certificate.json`). There is an alternative that uses only the source's own sup formula: P_78·100^79 > 79²·78!·173^79, so (d_78/79²)^{1/79} > 1.73. This needs no new inequality, only the exact value of P_78.

## 3. Proof

### 3.1 Pair count
Let P_n = #{(σ, τ) ∈ S_n × S_n : s(σ) = s(τ)}. Then P_n = Σ_y |s⁻¹(y)|², so d_n = P_n / n!.

### 3.2 Doubling lemma (from source inequality (1))
Source inequality (1), with a = m−1 and b = n−1, gives d_a d_b ≤ (a+b+1) d_{a+b+1}. Take a = b: d_a² ≤ (2a+1) d_{2a+1}.

Define a_0 = a and a_{k+1} = 2a_k + 1, so a_k + 1 = 2^k (a+1). Let u_k = log d_{a_k} / (a_k + 1). Then
u_{k+1} ≥ u_k − log(a_{k+1}+1)/(a_{k+1}+1),
so u_k ≥ u_0 − Σ_{j≥1} (j log 2 + log(a+1)) / (2^j (a+1)) = u_0 − (log 4 + log(a+1))/(a+1).

If d_n^{1/n} → L, then L = lim_k exp(u_k (a_k+1)/a_k) ≥ (d_a / (4(a+1)))^{1/(a+1)}. Existence of the limit is not even needed: the bound holds for limsup along the subsequence a_k. Taking a = 50 gives L ≥ 1.73308.

### 3.3 Exact formula for P_n (new ingredient)

(a) Decreasing binary trees. Each σ ∈ S_n corresponds to a unique decreasing binary plane tree T(σ): the root is n, the left subtree is T(L) and the right subtree is T(R), where σ = L n R. The in-order reading of T(σ) is σ. By induction on n, s(σ) is the postorder reading of T(σ), since post(T(σ)) = post(T(L)) post(T(R)) n = s(L) s(R) n.

(b) Shapes and labellings. A decreasing tree is a shape B (an unlabelled binary plane tree with n nodes) together with a labelling that decreases from parent to child. Index the nodes of B by postorder position 1..n. The postorder word of the labelled tree is w = (λ(1), …, λ(n)). Therefore s(σ) = s(τ) exactly when the two trees have the same position labelling w. Hence
P_n = Σ_{(B,B')} #{w ∈ S_n : w_i < w_j whenever i is a proper descendant of j in B or in B'} = Σ_{(B,B')} e(Q_{B,B'}),
where Q_{B,B'} is the transitive closure of the two descendant orders and e counts linear extensions.

(c) Closure lemma. In postorder, the descendant set of node j in B (including j) is an interval [j − a_j + 1, j]. Let D(j) be the smallest set that contains j and is closed under taking B-descendants and B'-descendants. Build it iteratively from {j}, each time adding an interval that contains a point already in the set and has right end at most j. This keeps the set an interval with right end j, so D(j) = [m_j, j]. If i ∈ D(j) then D(i) ⊆ D(j). If i < j and i ∉ D(j), then i < m_j and D(i) ⊆ [1, i] is disjoint from D(j). So the family {D(j)} is laminar, and i <_Q j holds iff i ∈ D(j) \ {j}. Hence Q is a rooted forest poset, in which the elements above any node form a chain.

(d) Hook-length formula for forests (Knuth, TAOCP Vol. 3, §5.1.4, Exercise 20; standard). For a forest poset, e(Q) = n! / Π_j |D(j)|. Therefore
d_n = Σ_{(B,B')} Π_{j=1}^n 1/h_j, with h_j = j − m_j + 1.
This was checked against brute force for n ≤ 6 (`scripts/stack_deg_shapes.py`).

(e) Block recursion. A forest pair (F, F') on [1, M] consists of two sequences of binary trees, with R and S trees respectively, whose postorders tile [1, M]. A cut point of F is the start position (≥ 2) of one of its trees. A common cut point c belongs to both F and F'. No generating interval crosses c, so no D(j) crosses c. The weight w = Π 1/h_j therefore factorizes over the blocks between consecutive common cut points. This gives a bijection between forest pairs and sequences of irreducible pairs (pairs with no common cut point), so
X(R, S, M) = Σ_{first block (r₁, s₁, m₁)} I(r₁, s₁, m₁) X(R − r₁, S − s₁, M − m₁), with X(0, 0, 0) = 1.

Take an irreducible pair on [1, m] with m ≥ 2. Node m is the root of both last trees, T_r and T'_s, and D(m) = [1, m]. Proof: if m_m = c > 1, then the last F-tree that meets c − 1 must end at c − 1. Otherwise its root, which lies in D(m), would have c − 1 as a descendant. So c is an F cut point, and likewise an F' cut point, which contradicts irreducibility. Hence h_m = m.

Now delete node m. The root of T_r had t ∈ {0, 1, 2} children, with multiplicity μ(0) = 1, μ(1) = 2 (left or right child), μ(2) = 1. Deletion leaves a forest pair on [1, m−1] with R = r−1+t and S = s−1+u trees, and all D(j) for j < m are unchanged. The cut points of the original pair are:
- the starts of reduced trees 2..min(r, R);
- the position m, if t = 0 (and likewise for F' with u).
So the original pair is irreducible iff two conditions hold:
- t and u are not both 0;
- no block boundary of the reduced pair has (cumulative F-tree count < min(r, R) and cumulative F'-tree count < min(s, S)).
Cumulative counts increase from left to right, so the second condition is equivalent to: the first block, if it is not the whole pair, has r₁ ≥ min(r, R) or s₁ ≥ min(s, S). This defines Y. Thus
I(r, s, m) = (1/m) Σ_{(t,u) ≠ (0,0)} μ(t) μ(u) Y^{(min(r,R), min(s,S))}(R, S, m−1), with I(1, 1, 1) = 1,
and d_n = I(1, 1, n), because a pair of single trees has no cut points.

The integer version (`scripts/stack_pairs_int.py`) multiplies by m!. Concatenating labelled blocks then contributes binomial coefficients, and P_n = n!·I(1, 1, n).

### 3.4 Verification of the computation (diagnostics; the proof is 3.3)
- The DP equals brute force for n ≤ 10 (`logs/stack_deg_brute.log` vs `logs/stack_deg_dp_check2.log`; P_10 = 2322885008).
- An independently derived left-to-right two-stack automaton over block states (`scripts/stack_deg_automaton.py`) equals the DP exactly for n ≤ 14. It was killed by the RSS cap at n = 15, as designed.
- Exact P_1..P_82 are in `outputs/stack_pairs_P_1_82.json` (sha256 a6e6efe6…b287), computed in 58.6 s with a peak RSS of 61 MB.
- No algebraic equation (degree ≤ 6, coefficient degree ≤ 11, as fit allows) and no linear recurrence (order ≤ 7) was found for d_n (`scripts/stack_guess.py`).

## 4. Significance and novelty assessment (for root)
- The refutation is not derivable from the source's own theorems. Theorem 2.5 only supplies the Fekete-type bound, and the authors state that an exact formula "seems out of reach". Defant's later free-probability lower bound stopped at 1.62924, and brute force stops near n = 14. The new ingredient is the closure lemma plus the hook-length formula, which makes d_n polynomial-time computable (about n⁶). The limit is ≈ 1.953, far outside the conjectured window.
- Why the authors' heuristic failed: they averaged |s⁻¹(s(π))|^{1/n}, which approximates exp(E log X / n), the typical growth. The degree is (E X)^{1/n}, and log X has variance linear in n.
- Not a classical extremal example, not a convention boundary, and not a printed construction in a cited paper.
- Registry path screens (Omega c7f3e33e D5 and Problems, OpenAI/math 4eaee875 preprints listing): no stack-sorting degree items. These are path screens only.

## 5. Lean plan and cost (honest)
Endpoint (literal source quantity):
`¬ ∃ L : ℝ, Tendsto (fun n => (deg n : ℝ) ^ (1 / (n : ℝ))) atTop (𝓝 L) ∧ 1.68 < L ∧ L < 1.73`,
where `deg n = (Σ_{y : Perm (Fin n)} (card (s⁻¹ y))²) / n!` and s is defined literally.

Required pieces:
1. A literal stack-sorting map on `Perm (Fin n)`, with a bridge to a list version.
2. The doubling inequality P_a² · C(2a, a) ≤ P_{2a+1}, via the source's injection; this needs standardization lemmas.
3. Correctness of the P_n formula: the decreasing-tree bijection, the closure lemma, the forest hook-length formula (not in mathlib; an induction proof is short on paper but nontrivial to formalize), and the block recursion.
4. Kernel evaluation. Evaluating the DP at n = 50 is too heavy for `decide` without native_decide. A cheaper split is to evaluate the DP only up to n = 20. From there, the elementary lower recursion G_n ≥ 4G_{n−1} + Σ_{i=1}^{n−2} C(n−1, i) G_i G_{n−1−i} is easy to prove from the root decomposition. Iterating it to n = 300 and applying the doubling bound gives > 1.77 (`logs/stack_simple_rec2.log`: seeds to 20 give a 1.7725 bound). That costs about 45k big-integer operations in the kernel.

Estimated Lean cost: medium-high. Item 3 dominates. There are no analytic semantics beyond the elementary limit argument.
