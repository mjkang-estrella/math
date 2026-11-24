# The h*-polynomial of the stable set polytope of an odd antihole

*Claude Opus 5.5 produced the original proof, the first review, the Lean code and the manuscript. GPT-6.2 Sol performed the cross-model review and edited this manuscript on 2026-11-23.*

## Abstract

Davis and Kohl conjectured that for every n ≥ 4 the h*-polynomial of the stable set polytope of the complement of the cycle C_n equals the perfectly matchable set polynomial p(C_n; z), plus z^{(n+1)/2} when n is odd. They proved the even case. We prove the conjecture for every n ≥ 4. The argument is elementary. The lattice points of t·P_{C̄_n} are described by a cyclic greedy recursion, and a rank-two transfer matrix counts them. Both parities are checked in Lean 4 with Mathlib, against the literal convex hull and the literal definition of perfectly matchable sets.

## 1. The conjecture and the source's definitions

R. Davis and F. Kohl, *Perfectly matchable set polynomials and h*-polynomials for stable set polytopes of complements of graphs*, state Conjecture 3.15 in §3.1 of their July 2022 preprint. The bibliographic record for the journal article is *Discrete Mathematics* 347 (2024), 114018. [Preprint](https://arxiv.org/abs/2207.14759v1) · [Journal record](https://doi.org/10.1016/j.disc.2024.114018)

A set S is perfectly matchable in G if the induced graph G[S] has a perfect matching. The empty set qualifies. The coefficient of z^k in p(G; z) counts the perfectly matchable sets of size 2k.

The stable set polytope P_G is the convex hull of the indicator vectors of the independent sets of G. For a lattice polytope P, the Ehrhart series ∑_{t≥0} |tP ∩ ℤ^n| z^t has numerator h*(P; z) over the denominator (1 − z)^{dim P + 1}. Davis and Kohl write h̄*(G; z) for h*(P_Ḡ; z).

**Conjecture 3.15.** For every n ≥ 4,

 h̄*(C_n; z) = p(C_n; z) + ((1 + (−1)^{n+1})/2) z^{(n+1)/2}.

The last term vanishes for even n. The preprint proves the even case in Corollary 3.14 and gives the odd examples n = 5, 7 and 9 in Table 2.

### Lean counterparts (module `AHDefs`)

| Source | Lean |
|---|---|
| χ(S) | `indicatorVec S : Fin n → ℝ`, value 1 on S and 0 off S |
| P_G = conv{χ(S) : S stable in G} | `stabPolytope G = convexHull ℝ {v \| ∃ S : Finset (Fin n), G.IsIndepSet ↑S ∧ v = indicatorVec S}` |
| P_{C̄_n} | `P n = stabPolytope (SimpleGraph.cycleGraph n)ᶜ` (Mathlib's cycle graph on `Fin n`; complement taken in Mathlib) |
| L(t) = \|tP ∩ ℤ^n\| | `ehr n t = Nat.card {x : Fin n → ℤ // (fun i => (x i : ℝ)) ∈ (t : ℝ) • P n}` |
| S perfectly matchable | `IsPerfectlyMatchable G S := ∃ M : G.Subgraph, M.verts = S ∧ M.IsMatching`. A subgraph of G with vertex set S in which every vertex has exactly one neighbour is exactly a perfect matching of G[S]. The empty set qualifies (M = ⊥). |
| p_{2k} | `pmCount n k = #{S : Finset (Fin n) \| S.card = 2k ∧ IsPerfectlyMatchable (cycleGraph n) S}` |
| p(C_n; z) = Σ_{k=0}^{⌊n/2⌋} p_{2k} z^k | `pmPoly n = Σ_{k ∈ range (n/2+1)} C (pmCount n k) * X^k` |
| h*(P; z) with dim P + 1 = n + 1 | the identity `PowerSeries.mk (ehr n ·) * (1 − X)^(n+1) = h`. Full dimension is `vectorSpan_P : vectorSpan ℝ (P n) = ⊤`, and `ehr_zero : ehr n 0 = 1` matches the source's constant term 1. |

Main theorem in Lean (`AHMain`):

```lean
theorem davis_kohl_conjecture_3_15 : Conjecture315
-- Conjecture315 : ∀ n, 4 ≤ n →
--   PowerSeries.mk (fun t => (ehr n t : ℤ)) * (1 - PowerSeries.X) ^ (n + 1) =
--     ((pmPoly n + (if Odd n then Polynomial.X ^ ((n + 1) / 2) else 0) : Polynomial ℤ) : PowerSeries ℤ)
theorem davis_kohl_conjecture_3_15_literal (n : ℕ) (hn : 4 ≤ n) :
    mk (fun t => (ehr n t : ℤ)) * (1 - X) ^ (n + 1) =
      ((pmPoly n + Polynomial.C ((1 + (-1 : ℤ) ^ (n + 1)) / 2) * Polynomial.X ^ ((n + 1) / 2) :
        Polynomial ℤ) : PowerSeries ℤ)
```

The axioms used are propext, Classical.choice and Quot.sound.

## 2. Theorem

**Theorem.** For every n ≥ 4,
 h*(P_{C̄_n}; z) = p(C_n; z) + [n odd] z^{(n+1)/2}.

Moreover p(C_n; z) + [n even] z^{n/2} = μ(C_n; z) := Σ_{M a matching of C_n} z^{|M|}. This is the Lucas polynomial L_n(z) = Σ_{j=0}^{⌊n/2⌋} (n/(n−j)) C(n−j, j) z^j. The closed form is classical and is not used below.

## 3. Proof

Throughout, n ≥ 4, indices are taken mod n, e_i are the unit vectors, w_i = e_i + e_{i+1}, and |x| = Σ x_i. Truncated subtraction on ℕ is written a ∸ b = max(0, a − b).

### 3.1 The polytope and its valid inequalities

A set S is stable in C̄_n exactly when it is a clique of C_n. For n ≥ 4 a clique has at most two vertices: three pairwise adjacent vertices would force 2 ≡ ±1 mod n. So P := P_{C̄_n} = conv{0, e_i, w_i}. Each of the following linear functionals is bounded on these generators, so for t ≥ 0 and v ∈ tP:

- (V1) v_i ≥ 0;
- (V2) v(I) ≤ t for every stable set I of C_n, since a clique meets I at most once;
- (V3) |v| ≤ 2t.

P contains 0 and every e_i, so it is full-dimensional and the exponent in the definition of h* is n + 1. (Lean: `smulP_nonneg`, `smulP_stable`, `smulP_sum`, `clique_card_le`, `vectorSpan_P`.)

**Covers.** P is convex and contains 0, so sP + rP = (s + r)P for s, r ≥ 0, and sP ⊆ tP for s ≤ t. Hence for s, y ∈ ℕ^n, the vector with coordinates s_i + y_i + y_{i−1} (s_i copies of e_i and y_i copies of w_i) lies in (Σ_i (s_i + y_i))·P. (`cover_mem`, `mem_smul_mono`.)

### 3.2 The cyclic greedy residual

Fix x ∈ ℕ^n. A *residual* of x is d ∈ ℕ^n with d_{i+1} = x_{i+1} ∸ d_i for all i. For a ∈ ℕ let o_a(0) = a and o_a(k+1) = x_{k+1} ∸ o_a(k), and put F(a) = o_a(n). Residuals correspond to fixed points of F via d ↦ d_0, and d_i = o_{d_0}(i) (`res_orb`, `res_of_fixed`).

**Lemma 1 (parity comparison).** If u ≤ v, then for even k: o_u(k) ≤ o_v(k) ≤ o_u(k) + (v − u). For odd k: o_v(k) ≤ o_u(k) ≤ o_v(k) + (v − u).

*Proof.* The map c ↦ x ∸ c is non-increasing and 1-Lipschitz. Induct on k, using the Lipschitz bound at each step. ∎ (`orb_succ_cmp`, `orb_mono`)

**Lemma 2 (tight pairs).** Suppose F(a) ≠ F(a + 1). Then for all k ≤ n, o_{a+1}(k) = o_a(k) + 1 if k is even and o_a(k) = o_{a+1}(k) + 1 if k is odd. Moreover x_k = o_a(k−1) + o_a(k) = o_{a+1}(k−1) + o_{a+1}(k) for 1 ≤ k ≤ n.

*Proof.* Once the two orbits agree they agree from then on, so they differ at every k ≤ n. By Lemma 1 they differ by exactly 1. The step c ↦ x ∸ c keeps two consecutive values distinct only if x is at least the larger one, and then neither step truncates. ∎ (`tight_pair`)

Let X(ν)_i := ν_{i−1} + ν_i + 1 for ν ∈ ℕ^n. In other words X(ν) = Σ ν_i w_i + 𝟙.

**Lemma 3 (odd n).**
- (a) x has at most one residual.
- (b) If x has no residual, then x = X(ν) for some ν.
- (c) X(ν) has no residual.
- (d) ν ↦ X(ν) is injective.

*Proof.* (a) For odd n, F is non-increasing by Lemma 1, so two fixed points u < v would give v = F(v) ≤ F(u) = u.

(b) Let b be least with F(b) ≤ b; such b exists because F(b) ≤ x_0. Since there is no fixed point, b ≥ 1 and F(b − 1) ≥ b. Lemma 1 gives F(b) ≤ F(b − 1) ≤ F(b) + 1, so F(b − 1) = b and F(b) = b − 1. Apply Lemma 2 with a = b − 1 and take ν_i = o_a(i) − [i odd]. Each subtraction is valid by the parity comparison in Lemma 2. For i = 0, the final tight step reads x_0 = o_a(n−1) + F(a) = ν_{n−1} + ν_0 + 1, since n−1 is even and F(a) = a + 1.

(c) A direct computation for x = X(ν) gives o_{ν_0}(k) = ν_k + [k odd] and o_{ν_0+1}(k) = ν_k + [k even] for k < n. Hence F(ν_0) = ν_0 + 1 and F(ν_0 + 1) = ν_0. If a ≤ ν_0, then F(a) ≥ F(ν_0) > a. If a > ν_0, then F(a) ≤ F(ν_0 + 1) < a.

(d) By (c), ν_0 is determined by x = X(ν): it is the a with F(a) > a ≥ F(a + 1). The orbit from ν_0 then determines every ν_k. ∎ (`res_unique`, `no_res_odd`, `xv_of_no_res`, `xv_no_res`, `xv_injective`)

**Lemma 4 (even n).**
- (a) x has a residual.
- (b) If d and d' are residuals with d'_0 < d_0, then o_{d_0 − 1} is also a residual.
- (c) If d and d' are residuals with d'_0 + 1 = d_0, then x = X(e) and d = e + [i even], where e_i = d_i − [i even].
- (d) Conversely, X(e) has the two residuals e + [i even] and e + [i odd].

*Proof.* For even n, F is non-decreasing and 1-Lipschitz.

(a) Let b be least with F(b) ≤ b. Then F(b) = b: either b = 0, or F(b) ≥ F(b − 1) ≥ b.

(b) With c = d_0 − 1, monotonicity and the Lipschitz bound give F(c) ≤ F(d'_0) + (c − d'_0) = c and F(c) ≥ F(d_0) − (d_0 − c) = c.

(c) Lemma 2 with a = d'_0.

(d) X(e)_i = d_{i−1} + d_i for both choices of d, because the parity indicators of i − 1 and i sum to 1, including at i = 0 since n is even. A vector with x_i = d_{i−1} + d_i for all i has d as a residual. ∎ (`res_exists`, `res_pred`, `xv_of_two_res`, `pair_struct`, `xv_res_even`)

### 3.3 Lattice points of tP

**Lemma 5 (certificate).** Let d be a residual of x.
- (a) If d_j = 0 for some j, there is a stable set I of C_n with x(I) = |d|.
- (b) If every d_i ≥ 1, then |x| = 2|d|.

*Proof.* (a) Cut the cycle at j: put x'_k = x_{j+k} and d'_k = d_{j+k}, so d'_0 = 0 and d'_{k+1} = x'_{k+1} ∸ d'_k. By induction on m there are sets I_m ⊆ [1, m] and J_m ⊆ [1, m − 1], each without two consecutive integers, with x'(I_m) = D_m and x'(J_m) + d'_m = D_m, where D_m = d'_1 + ⋯ + d'_m. For m = 1, take I_1 = {1} and J_1 = ∅, since d'_1 = x'_1. For the induction step:
- if d'_{m+1} = 0, take I_{m+1} = J_{m+1} = I_m;
- otherwise x'_{m+1} = d'_{m+1} + d'_m, and we take I_{m+1} = J_m ∪ {m+1} and J_{m+1} = I_m.

At m = n we have d'_n = d_j = 0. The image of J_n ⊆ [1, n − 1] under k ↦ j + k is a stable set of C_n of weight D_n = |d|.

(b) In this case x_{i+1} = d_i + d_{i+1} for every i; sum over i. ∎ (`path_cert`, `stable_cert`, `sum_x_of_pos`)

Define κ(x) = |d| if x has a residual d (using a chosen one), and κ(x) = ⌈|x|/2⌉ otherwise.

**Theorem 6.** For x ∈ ℕ^n and t ∈ ℕ: x ∈ tP ⟺ κ(x) ≤ t. Moreover κ(x) = |d| for every residual d of x, and for odd n, κ(X(ν)) = |ν| + (n+1)/2.

*Proof.* Suppose first that x has a residual d.
- (⇐) Set y_i = min(x_{i+1}, d_i) and s_i = d_i − y_i. Then s_i + y_i + y_{i−1} = x_i and Σ(s_i + y_i) = |d|, so x ∈ |d|P ⊆ tP.
- (⇒) Use Lemma 5 together with (V2) or (V3).
Since every residual satisfies the same equivalence, all residuals of x have the same sum.

Suppose x has no residual. Then n is odd by Lemma 4(a), and x = X(ν) by Lemma 3(b).
- (⇐) X(ν) − e_0 is covered by y_i = ν_i + [i odd] copies of w_i, because the parity indicators of i − 1 and i sum to 1 for i ≠ 0 and to 0 for i = 0. Hence X(ν) ∈ (|ν| + (n−1)/2 + 1)P.
- (⇒) (V3) gives 2|ν| + n = |X(ν)| ≤ 2t. ∎ (`res_cover`, `xv_cover`, `res_mem_iff`, `xv_mem_iff`, `kappa_of_res`, `kappa_of_xv`, `mem_iff_kappa`)

By (V1) and (V2) with I = {i}, every integer point of tP lies in ℕ^n with coordinates at most t. So L(t) = #{x ∈ ℕ^n : κ(x) ≤ t}, and each such x has x_i ≤ κ(x) (`ehr_eq_card`, `mem_box_of_kappa`).

### 3.4 Counting

Let A(t) = #{x : κ(x) = t}. Then L(t) = Σ_{s≤t} A(s) (`ehr_eq_sum`).

For fixed d, the vectors x having d as a residual are given coordinatewise:
- x_i = d_{i−1} + d_i if d_i ≥ 1;
- x_i ∈ {0, …, d_{i−1}} if d_i = 0.

Their number is Π_i w(d_i, d_{i+1}), where w(u, v) = u + 1 if v = 0 and w(u, v) = 1 otherwise (`mem_resSet`, `card_resSet_eq`). Put
- B(t) = Σ_{|d| = t} #{x : d is a residual of x},
- E(t) = #{e ∈ ℕ^n : |e| = t}.

**Lemma 7.**
- If n is odd, A(t) = B(t) + [t ≥ (n+1)/2] · E(t − (n+1)/2).
- If n is even, A(t) + [t ≥ n/2] · E(t − n/2) = B(t).

*Proof.* Odd n: by Lemma 3(a), x ↦ its residual splits the x with residual and κ = t disjointly over the d with |d| = t. By Lemma 3(b)–(d) and Theorem 6, the x without residual and with κ = t are the X(ν) with |ν| = t − (n+1)/2, each counted once.

Even n: count the pairs (d, x), where d is a residual of x and |d| = t.
- The pairs in which d has the least d_0 among the residuals of x are in bijection with {x : κ(x) = t}, by Lemma 4(a) and because a residual is determined by d_0.
- By Lemma 4(b)–(d), the remaining pairs are in bijection with {e : |e| = t − n/2} via (d, x) ↦ d − [i even] and e ↦ (e + [i even], X(e)). Here |e + [i even]| = |e| + n/2. ∎ (`A_odd`, `A_even`)

### 3.5 Generating functions

Let G be the 2 × 2 matrix of power series with rows and columns indexed by the type of d_i (0: d_i ≥ 1; 1: d_i = 0):

 G = [[a, b], [1, 1]], where a = Σ_{m≥1} z^m and b = Σ_{m≥1} (m+1) z^m.

A matrix entry G(s_i, s_{i+1}) sums w(d_i, d_{i+1})z^{d_i} over the possible current values d_i of type s_i, with the next type s_{i+1} prescribing whether d_{i+1} vanishes. For any finite square matrix M, tr(M^n) = Σ_{s} Π_i M(s_i, s_{i+1}), the sum running over cyclic sequences s of length n (`trace_pow_eq_cyclic`, proved by an open-walk induction). Take M = G and extract the coefficient of z^t with the product rule for power series. For each d, only the type sequence of d contributes, and it contributes Π_i w(d_i, d_{i+1}). Hence Σ_t B(t) z^t = tr(G^n) (`sum_types`, `coeff_trace_G`).

Next, (1 − z)a = z and (1 − z)²b = z(2 − z). Hence Q := (1 − z)G has tr Q = 1 and det Q = −z (`trace_Q`, `det_Q`). The matching transfer matrix K = [[1, 1], [z, 0]] (state 1 means the edge {i, i+1} is used) also has trace 1 and determinant −z. For 2 × 2 matrices, Q² = (tr Q)Q − (det Q)I, so the sequences tr(Q^k) and tr(K^k) satisfy the same recurrence t_{k+2} = t_{k+1} + z t_k with the same initial values 2 and 1. Therefore

 (1 − z)^n Σ_t B(t) z^t = tr(K^n) (`trace_pow_rec`, `trace_pow_eq_of`, `B_gen`).

Finally, (Σ_t E(t) z^t)(1 − z)^n = ((Σ_m z^m)(1 − z))^n = 1 (`E_gen`).

### 3.6 Matchings and perfectly matchable sets

Encode a matching of C_n as m ∈ {0, 1}^n (m_i = 1 iff the edge {i, i+1} is used) with no two cyclically consecutive ones. Then tr(K^n) = Σ_m z^{|m|} = μ(C_n; z) (`trace_K_pow`). Let V(m) = {i : m_i = 1 or m_{i−1} = 1}.

- (i) |V(m)| = 2|m|.
- (ii) V(m) is perfectly matchable: the subgraph whose edges are {i, i+1} with m_i = 1 is a matching with vertex set V(m).
- (iii) Every perfectly matchable S equals V(m) for some m: given a matching subgraph M with vertex set S, set m_i = [M uses {i, i+1}]. Two consecutive ones would give vertex i+1 two partners, so m is a matching; and a vertex lies in S iff it is matched, iff m_i = 1 or m_{i−1} = 1.
- (iv) If V(m) = V(m') ≠ V then m = m'. Start at a vertex j ∉ V(m); there m_j = m'_j = 0. Going around the cycle, m_{p+1} is forced: it is 0 if m_p = 1, and it is [p+1 ∈ V(m)] if m_p = 0.
- (v) V(m) = V forces m to alternate. So n is even, and the matchings covering V are exactly the two alternating sequences.

Grouping matchings by V(m):

 μ(C_n; z) = Σ_{S perfectly matchable} z^{|S|/2} + [n even] z^{n/2} = p(C_n; z) + [n even] z^{n/2} (`card_vset`, `pm_of_valid`, `valid_of_pm`, `valid_unique`, `eq_alt`, `fiber_univ_card`, `pmPoly_eq_sum`, `pmPoly_add`).

### 3.7 Assembly

(Σ_t L(t) z^t)(1 − z)^{n+1} = (Σ_t A(t) z^t)(1 − z)^n, by L(t) = Σ_{s≤t} A(s).

- Odd n: Lemma 7 and §3.5 give μ(C_n; z) + z^{(n+1)/2} = p(C_n; z) + z^{(n+1)/2}.
- Even n: they give μ(C_n; z) − z^{n/2} = p(C_n; z).

∎ (`hstar_formula`)

**Check against the source's Table 2** (Lean `table2_n4` … `table2_n7`, derived from the theorem and the recurrence for tr(K^n)):

| n | h̄*(C_n; z) |
|---|---|
| 4 | 1 + 4z + z² |
| 5 | 1 + 5z + 5z² + z³ |
| 6 | 1 + 6z + 9z² + z³ |
| 7 | 1 + 7z + 14z² + 7z³ + z⁴ |

All four agree with Table 2.

## 4. Remarks on the route

The written proof in lane t1-pool125 treats odd n only and cites the source's Corollary 3.14 for even n. This manuscript and the Lean development prove both parities. Even n reuses the same machinery: existence and the interval property of residuals, plus the bijection with half-integral vectors.

Two further departures from lane t1-pool125:
- The stable-set lower bound is proved by an explicit two-set path recursion instead of the dynamic-programming argument.
- The Lucas closed form is replaced by the equality of traces of two 2 × 2 matrices with the same trace and determinant.

## 5. Significance

The new case beyond the preprint’s proved range is odd n ≥ 5. The graph C_n is then outside the bipartite hypothesis of Davis and Kohl’s Lemma 3.11. The known facet description of the odd antihole gives the least integral dilate containing a nonnegative integer vector x as the maximum of its largest stable-set weight on C_n and ⌈∑ x_i/2⌉. The cyclic residual computes that value in a form suitable for enumeration. Its integer fixed points produce the matching polynomial through the rank-two transfer calculation, and the half-integral family contributes the single extra monomial. [Davis–Kohl, §3.1](https://arxiv.org/abs/2207.14759v1) · [Wagler, §§2–3, for the facet description](https://webdoc.sub.gwdg.de/ebook/e/2003/zib_3/reports/ZR-02-07.pdf)

## 6. Related work and source status

The arXiv record has one version, in which the odd case is conjectural. The Crossref and OpenAlex journal records, the Aalto abstract and the zbMATH Open review do not establish the odd case’s status in the published text. The journal text remains unread. [Crossref](https://api.crossref.org/works/10.1016/j.disc.2024.114018) · [OpenAlex](https://openalex.org/W4393965361) · [Aalto](https://research.aalto.fi/en/publications/perfectly-matchable-set-polynomials-and-h-polynomials-for-stable-/) · [zbMATH Open](https://zbmath.org/7851566)

The two related works indexed as citations by OpenAlex concern perfectly matchable subgraph polytopes and path and cyclic block polytopes. Braun and Solus obtain the Lucas polynomial for certain stable hypersimplices. The odd antihole considered here has the additional monomial in its numerator. Searches of the omega registry, Principia records and the web found no prior proof of the odd identity. [Mori](https://arxiv.org/abs/2210.17147) · [Jiang–Yang–Zhong](https://arxiv.org/abs/2607.22008) · [Braun–Solus](https://arxiv.org/abs/1408.4713)

## 7. Formal verification

- Lean 4.34.1 with Mathlib at revision d13f23b7, using specific imports only.
- 13 modules, 2,073 lines (see LEAN-SOURCE-APPENDIX.md).
- Every module was compiled and checked with leanchecker in a clean build (receipts `clean2-*`).
- The packet’s replay in `replay-final/` rebuilt the modules from the appendix and matched all author oleans byte for byte. A separate root replay also reported success for all 13 modules and confirmed that the appendix matched the author sources.
- The endpoints depend only on propext, Classical.choice and Quot.sound.
