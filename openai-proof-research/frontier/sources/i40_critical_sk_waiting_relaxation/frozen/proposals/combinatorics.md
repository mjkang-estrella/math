> Archived exploratory draft. Some claims were corrected, rejected, or left unreviewed. Use [the final index](../README.md) and [screening decisions](../SCREENING.md) for accepted results.

# Combinatorics and discrete probability lane: downstream consequences

Pinned upstream: `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. I assume every upstream theorem is true, as the project rules require. Everything below is a deduction from upstream theorems; none of it audits them. Sources were fetched into `sources/cache/combinatorics/` from `https://raw.githubusercontent.com/openai/math/<sha>/preprints/<dir>/build/...`. Checks: `experiments/combinatorics.py`, run with `python3 -I`; it needs `networkx`.

## Ranking

| # | Candidate | Upstream input | Status |
|---|---|---|---|
| A | Point/unit-circle incidences for **unbalanced** sizes with a power saving; corollaries for rich points and congruent copies | 167 (unit distances) | **Proved below.** Strongest result. As far as I know, new because 167 is new. |
| B | Exact multicolour cycle–clique Ramsey numbers in the full range m ≥ R(n_1,…,n_k) | 189 (cycle–clique) | **Proved below.** Extends a known range (Madarasi 2020 needs m ≥ 4κ+2). Small increment. |
| C | Largest chromatic number of K_s-free n-vertex graphs: logarithmic exponent determined, s ≥ 5 | 170 (r(s,t)) | Proved (sketch-complete). A standard translation, so low novelty. |
| — | Rejected candidates: see the final section | 159, 160, 156, 165, 171, 173, 180 | |

---

## A. Unbalanced unit-circle incidences with a power saving

**Source.** Family 167, *A power saving for planar unit distances*, `preprints/A-power-saving-for-planar-unit-distances-September-23-2026/`, Theorem `thm:main`. There are absolute constants C₀ and 1 ≤ β < 4/3 such that u(n) ≤ C₀ n^β for every n. Here u(n) is the largest number of unordered pairs at distance 1 among n points of ℝ². Write δ = 4/3 − β > 0.

The companion is a balanced unit-distance statement. Its internal incidence proposition (`inc:incidence`) is the log-weakened Szemerédi–Trotter bound. It does not contain the unbalanced statement below, nor the corollaries.

**Notation.** For finite P, Q ⊂ ℝ², set I(P,Q) = #{(p,q) ∈ P×Q : |p−q| = 1}. This is the number of incidences between P and the unit circles centred at Q. The definition is symmetric: I(P,Q) = I(Q,P).

### Theorem A
There is an absolute constant K such that, for all finite P, Q ⊂ ℝ² with |P| = m ≥ |Q| = n ≥ 1,

  I(P,Q) ≤ K ( m^{2−β} n^{2β−2} + m ) = K ( (mn)^{2/3} (m/n²)^{δ} + m ).

By symmetry the same bound holds with m and n swapped. So in the whole range n ≤ m ≤ n^{2−ε}, the bound gains a factor (n²/m)^δ ≥ n^{εδ} over the Spencer–Szemerédi–Trotter bound O((mn)^{2/3} + m + n). At m = n it recovers u(n) ≲ n^β.

### Proof
**Step 0 (crude unbalanced bound).** Let m′ ≥ n′ ≥ 1. Split P′ into at most ⌈m′/n′⌉ ≤ 2m′/n′ groups G, each of size at most n′.

The map (p,q) ↦ {p,q} sends incidences between G and Q′ to unit-distance pairs in G ∪ Q′. Each pair has at most 2 preimages. Also |G ∪ Q′| ≤ 2n′ and u is nondecreasing. So I(G,Q′) ≤ 2u(2n′) ≤ 2^{1+β} C₀ n′^β. Summing over the groups gives:

  I(P′,Q′) ≤ A (m′ n′^{β−1} + n′ m′^{β−1}),  A = 2^{2+β} C₀,   (∗)

for all m′, n′ ≥ 1. The second term covers the case m′ < n′, by symmetry.

**Step 1 (range m ≥ n²).** The incidence graph has no K_{2,3} with the 2 on the circle side, because two distinct unit circles meet in at most 2 points. Kővári–Sós–Turán then gives I ≤ C(n m^{1/2} + m) ≤ 2Cm.

**Step 2 (range n ≤ m ≤ n²; polynomial partitioning).** Put D = ⌊m/n⌋. Then 1 ≤ D, m/(2n) ≤ D ≤ m/n, and D² ≤ m. The Guth–Katz partitioning theorem gives a nonzero f with deg f ≤ D. The complement ℝ² \ Z(f) has L ≤ C₂D² connected cells, and each cell contains at most C₁m/D² points of P.

- *Circles contained in Z(f).* Such a circle's polynomial (x−a)²+(y−b)²−1 is irreducible over ℂ. Since f vanishes on infinitely many of its points, Bézout shows it divides f. Distinct centres give non-associate factors, so at most D/2 circles lie in Z(f).
  - Let Γ₀ be these circles. Each point has degree d_p ≤ 1 + C(d_p, 2) in the incidence graph. Two circles share at most 2 points. Hence I(P, Γ₀) ≤ m + 2C(|Γ₀|, 2) ≤ m + D²/4 ≤ 2m.
- *Other circles, points on Z(f).* A circle not contained in Z(f) meets it in at most 2D points (Bézout). This contributes at most 2Dn ≤ 2m incidences.
- *Other circles, points inside cells.* Such a circle minus its at most 2D points of Z(f) has at most max(1, 2D) arcs. Each arc lies in one cell, so the circle meets at most 3D cells.
  - Let cell i contain m_i ≤ C₁m/D² points and meet n_i circles. Then Σn_i ≤ 3Dn.
  - Apply (∗) in each cell and use Σ_{i≤L} x_i^θ ≤ L^{1−θ}(Σx_i)^θ with θ = β−1 ∈ (0,1):
  - Σ m_i n_i^{β−1} ≤ (C₁m/D²)(C₂D²)^{2−β}(3Dn)^{β−1} ≲ m n^{β−1} D^{1−β} ≤ 2^{β−1} m^{2−β} n^{2β−2}. This uses 1−β < 0 and D ≥ m/2n.
  - Σ n_i m_i^{β−1} ≤ (C₁m/D²)^{β−1} · 3Dn ≲ n m^{β−1} D^{3−2β} ≤ m^{2−β} n^{2β−2}. This uses 3−2β > 0 and D ≤ m/n.

Adding the four contributions gives I ≤ K(m^{2−β}n^{2β−2} + m). Finally, m^{2−β}n^{2β−2} = (mn)^{2/3}(m/n²)^δ with β = 4/3 − δ. ∎

### Corollary A1 (rich points)
Let |Q| = n and P_r = {p : p lies on at least r unit circles centred in Q}. There are absolute r₀ and K′ such that, for r ≥ r₀,

  |P_r| ≤ K′ ( n² r^{−3/(1−3δ)} + n^{(2+3δ)/(1+6δ)} r^{−3/(1+6δ)} + n/r ).

Both exponents of r beat the Szemerédi–Trotter exponent 3.

*Proof.* Put x = |P_r|, so rx ≤ I(P_r, Q).
- If n ≤ x ≤ n²: Theorem A gives rx ≤ K(x^{2/3+δ}n^{2/3−2δ} + x). For r ≥ 2K this forces x^{1/3−δ} ≤ (2K/r)n^{2/3−2δ}.
- If x > n²: Step 1 gives rx ≤ 2Cx, which is impossible for large r.
- If x < n: the swapped form gives rx ≤ K(n^{2/3+δ}x^{2/3−2δ} + n). So either x ≤ 2Kn/r or x^{1/3+2δ} ≤ (2K/r)n^{2/3+δ}. ∎

### Corollary A2 (congruent copies)
Fix a planar configuration T = (t₁,…,t_k) with t₁ ≠ t₂. Count the maps g: T → P (|P| = n) that are restrictions of isometries of ℝ². There are at most 4u(n) = O(n^{4/3−δ}) of them, and the same bound holds for the number of copies as subsets.

*Proof.* The ordered pair (g(t₁), g(t₂)) is at distance |t₁t₂|; after rescaling there are at most 2u(n) such ordered pairs. At most two isometries of ℝ² send (t₁, t₂) to a given ordered pair. ∎

The reduction is classical: it is the route to the older O(n^{4/3}) bound for congruent triangles. Only the power saving is new, and it is inherited from 167.

**Corollary A3.** The number of pairs whose distance lies in a given set of k distances is at most k·u(n) = O(k n^{4/3−δ}). This beats the Pach–Sharir-type bound O(k^{2/3}n^{4/3}) when k < n^{3δ}.

**Sharpness.** The linear term m is attained: take m points on circles around n centres, so I ≥ m. For m ≥ n² Theorem A is therefore sharp up to constants. Elsewhere the true exponent is unknown, as for u(n) itself. The method is limited by β: putting the conjectural β = 1+o(1) into the same proof gives (mn)^{2/3}(m/n²)^{1/3}, which is m·n^{o(1)} at m = n.

**Checks.** `check_congruent_reduction` verifies the inequality "copies ≤ 4u" on 36-point square and triangular lattice patches (u = 60 with 0 copies; u = 85 with 50 copies). This is a sanity check only.

**Novelty.** The partition bootstrapping is the standard method. A web search ([Aronov et al. 1208.0053](https://arxiv.org/pdf/1208.0053), [Sharir–Solomon–Zlydenko 2003.02190](https://arxiv.org/pdf/2003.02190)) found no planar unbalanced unit-circle bound below (mn)^{2/3}, which is expected because none existed before 167. Status: **new as a consequence of 167**, technically routine.

**Open gaps.**
1. δ is non-quantitative upstream, so the bounds are non-quantitative too.
2. Extending to circles of k radii, or to unit circles on spheres in ℝ³, needs more than u(n).

---

## B. Multicolour cycle–clique Ramsey numbers, full range

**Source.** Family 189, *Cycle–clique Ramsey numbers*, `preprints/Cycle-clique-Ramsey-numbers-September-25-2026/`, Theorem `thm:main`: R(C_m, K_n) = (m−1)(n−1)+1 for all m ≥ n ≥ 3 with (m,n) ≠ (3,3).

### Theorem B
Let k ≥ 1 and n₁, …, n_k ≥ 2. Let κ = R(K_{n₁}, …, K_{n_k}) be the k-colour clique Ramsey number, and assume κ ≥ 3. Then for every m ≥ κ with (m, κ) ≠ (3, 3):

  R(C_m, K_{n₁}, …, K_{n_k}) = (m−1)(κ−1) + 1.

*Upper bound.* Take any (k+1)-colouring of K_M with M = (m−1)(κ−1)+1, where colour 0 is red. Merge colours 1, …, k into blue. Theorem 189 with n = κ gives a red C_m or a blue K_κ. The colouring restricted to a blue K_κ uses only colours 1, …, k, so by definition of κ it contains a K_{n_i} in colour i.

*Lower bound.* Fix a colouring c of K_{κ−1} with colours 1, …, k and no K_{n_i} in colour i; it exists by minimality of κ. On [κ−1] × [m−1], colour edges inside a block red and edges between blocks a and b with c(a,b).
- The red graph is a disjoint union of K_{m−1}'s, so it has no C_m.
- A colour-i clique of order n_i ≥ 2 has its vertices in distinct blocks, so it would project to a colour-i K_{n_i} in c. ∎

**Consequences.**
- R(C_m, K₃, K₄) = 8m − 7 for every m ≥ 9.
- R(C_m, K₃, K₃, K₃) = 16m − 15 for every m ≥ 17.
- R(C_m, K₅, K₅) = (m−1)(R(5,5)−1)+1 for all m ≥ R(5,5), even though R(5,5) itself is unknown.

**Corollary B1 (cycle spectrum).** Let G have N vertices and α(G) = a ≥ 2. Then G contains C_m for every m with a+1 ≤ m ≤ ⌊(N−1)/a⌋ + 1, except (m, a) = (3, 2), which needs N ≥ 6. The upper end is sharp: a disjoint copies of K_{m−1} have N = a(m−1) vertices and no C_m. (This is just Theorem 189 read as a statement about G and its complement.)

**Checks.**
- `check_multicolour_blowup` verifies the lower-bound colouring for R(C_m, K₃, K₃) at m = 6 and 7 (25 and 30 vertices): no red C_m and no monochromatic triangle in colour 2 or 3.
- `check_cycle_spectrum` verifies B1 exhaustively on every graph with at most 7 vertices (106 (G, m) instances) and checks the sharpness examples.

**Novelty.** Madarasi ([arXiv 2003.12691](https://arxiv.org/pdf/2003.12691)) proves the same identity, with the same blow-up lower bound, for m ≥ 4κ+2 via Nikiforov. Keevash–Long–Skokan cover κ ≥ κ₀ with an unspecified κ₀. Schiermeyer and Chen–Cheng–Zhang give κ = 6, 7. So the new content is the window κ ≤ m ≤ 4κ+1 for the finitely many small κ not otherwise covered (e.g. κ = 9, 14, 17, 18). Status: **known method, small new range.**

---

## C. Chromatic number of K_s-free graphs (s ≥ 5)

**Source.** Family 170 (`Sharp-Logarithmic-Exponents-for-Fixed-Off-Diagonal-Ramsey-Numbers`, Thm `intro:main`; and `r(5,t)`): t^{s−1}/(log t)^{s−2+ε} ≤ r(s,t) ≤ C_s t^{s−1}/(log t)^{s−2}.

**Claim.** Let f_s(n) be the largest χ(G) over K_s-free graphs G on n vertices. Then f_s(n) = n^{(s−2)/(s−1)} (log n)^{−(s−2)/(s−1) + o(1)}.

*Lower bound.* Take t = ⌈(2n(log n)^{s−2+ε})^{1/(s−1)}⌉. Then r(s,t) > n, so there is a K_s-free graph on n vertices with α < t, and χ ≥ n/t.

*Upper bound.* The AKS upper bound gives α ≥ c(m log^{s−2} m)^{1/(s−1)} for every K_s-free m-vertex graph. Greedily remove maximum independent sets dyadically down to n^{1/3} vertices, then colour the remaining vertices singly. The geometric sum gives O(n^{(s−2)/(s−1)} (log n)^{−(s−2)/(s−1)}).

Before 170, the known window for the log exponent was [(s−2)/(s−1), (2s−4)/(s−1)] (Bradač). Status: **routine translation**. This is new only in that 170 is new. s = 4 stays open, since 170 starts at s = 5.

---

## Rejected candidates (with reasons)

- **Quasipolynomial bound in r for W_r(k) (159 ⇒ vdW):** already in both companions. See the 160 intro display and the 159 section "Coloring thresholds", Eq. `ap:coloring`.
- **Weighted, harmonic-tail and dense-prime APs:** already in 159, `09-consequences.tex`.
- **Borsuk counterexamples in all dimensions d ≥ 9:** already in 156, Corollary `cor:higher-dimensions` (simplex adjunction).
- **Unconditional versions of conditional crossing-number results (165)**, e.g. join products, cr(K_{1,m,n}) bounds: plausible, but the conditional literature results could not be pinned down and verified in time. Left as a lead (gap).
- **Hypercube Ramsey (171):** r(H) = O(2^n) for H ⊆ Q_n and r(Q_m, Q_n) = Θ(2^n) are immediate. Linear Ramsey for products such as Q_a □ C_{2ℓ} follows by embedding in Q_{a+⌈log₂ℓ⌉+1}. True but too thin to propose.
- **173 (SNC) ⇒ Caccetta–Häggkvist cases:** I found no valid derivation; the obvious counting fails because N⁻(v) can be small.
- **180 (Barnette) ⇒ induced two-tree partitions of Eulerian triangulations:** this is a known equivalence via planar duality (cycle–cut), so a restatement.
- **170 ⇒ r(s+1,t)/r(s,t) → ∞:** already implied by Bradač's lower bound.

## Open gaps
1. In A, the constants are not explicit because β is non-quantitative upstream.
2. In B, the novelty claim depends on the KLS constant κ₀ being unspecified. If κ₀ is effectively small, the new window shrinks.
3. In C, the o(1) is not quantified, and s = 4 is open.
4. The lead on the 165 crossing-number literature is not pursued.
