# MathDB 343238: Abebe's generalized Brouwer inequality follows from published results

Status: **resolved in full scope by a short bridge from published (arXiv) results. Zero credit expected**, because this is a routine corollary of Lew 2025 plus a classical theorem. This note records the bridge for the root's coverage ledger. It is not a candidate.

## Statement (source: Abebe, arXiv:1907.07541 v1, Conjecture 3, TeX lines 86-91 and 389-392)

Let S be an abstract simplicial complex of dimension k−1. Let f_{k−1} be the number of its (k−1)-faces. Let λ_1 ≥ λ_2 ≥ … be the eigenvalues of L(S) = ∂_{k−1}∂_{k−1}^T, the up-Laplacian acting on C_{k−2}(S) (source Definition, TeX line 306). Then for every t ∈ ℕ,

  λ_1 + … + λ_t ≤ (k−1) f_{k−1} + C(t+k−1, k).

The MathDB record (corpus chunk line in results.json) states the same inequality.

## Ingredients

* **(KT)** Kothari and Tudose, *On Brouwer's Laplacian conjecture*, arXiv:2606.12197 (June 2026). It proves Brouwer's conjecture: for every graph, s_t(L) ≤ |E| + C(t+1, 2). This is exactly the case k = 2.
* **(Lew)** A. Lew, *Sums of Laplacian eigenvalues and sums of degrees*, arXiv:2508.04209 v1 (Aug 2025), Theorem 1.3 (TeX label thm:degree_bound). Let X be a complex, 1 ≤ r ≤ dim X and 1 ≤ t ≤ f_{r−1}(X)/(r+1). Then
  s_t(L^+_{r−1}(X)) ≤ (sum of the (r+1)t largest r-degrees of (r−1)-faces of X).
* **(LKK)** Lovász's form of the Kruskal–Katona theorem. Let F be a family of m-sets with |F| = C(x, m) for some real x ≥ m. Then its shadow (the set of (m−1)-subsets of members) has size at least C(x, m−1).
* **(Bin)** For integers r ≥ 2 and t ≥ 1, C(t+r, r) ≥ (r+1)t.
  Proof: at t = 1 both sides equal r+1. For t ≥ 2, C(t+r, r) = C(t+r, t) ≥ C(t+r, 2), because 2 ≤ min(t, r). Also C(t+r, 2) ≥ (r+1)t, which is equivalent to t² + r² − 3t − r ≥ 0. This holds since t² − 3t ≥ −2 and r² − r ≥ 2.

## Proof for k ≥ 3

Write r = k−1 ≥ 2. Then L(S) = L^+_{r−1}(S), and f_{k−1} = f_r is the number of r-faces (facets of top dimension). Let N = f_{r−1}(S).

**Case (r+1)t ≤ N.** By (Lew), s_t ≤ Σ_{ρ∈A} deg(ρ) for some set A of (r+1)t ridges. Each r-face σ has exactly r+1 ridges, so

  Σ_{ρ∈A} deg(ρ) = Σ_σ |{ρ ∈ A : ρ ⊂ σ}| ≤ r·f_r + |F'|,

where F' is the set of r-faces whose ridges all lie in A. The shadow of F' is contained in A, so it has at most (r+1)t elements, and (r+1)t ≤ C(t+r, r) by (Bin). Suppose |F'| > C(t+r, r+1). Write |F'| = C(x, r+1) with x > t+r. By (LKK) the shadow has at least C(x, r) > C(t+r, r) ≥ (r+1)t elements, which is a contradiction. (C(·, r) is strictly increasing on [r−1, ∞).) Hence |F'| ≤ C(t+r, r+1), and

  s_t ≤ r f_r + C(t+r, r+1) = (k−1) f_{k−1} + C(t+k−1, k).

**Case (r+1)t > N**, which also covers every t at or beyond the matrix size. The trace is (r+1) f_r, so s_t ≤ (r+1) f_r. The shadow of the family of all r-faces lies inside the N ridges, and N < (r+1)t ≤ C(t+r, r). By (LKK), f_r ≤ C(t+r, r+1), exactly as above. Hence s_t ≤ r f_r + f_r ≤ r f_r + C(t+r, r+1).

t = 0 is trivial. **Case k = 2** is Brouwer's conjecture, proved in (KT). ∎

## Novelty and credit assessment

* Lew (2025) cites Abebe and Abebe–Pfeffer and proposes a *stronger* conjecture: s_t ≤ f_r + C(t,2) + r t. He records only the weaker Corollary 1.4, s_t ≤ f_r + C((r+1)t, 2), and nowhere notes that Theorem 1.3 already implies Abebe's Conjecture 3 for r ≥ 2. Huang (arXiv:2607.20051, line 215) cites Abebe only as motivation. Zhang–Song–Fan (arXiv:2607.20910) do not cite Abebe, and their Brouwer-type bound ((r+1)/2·f_r + f_{r−2}/r·C(ℓ+1,2)) has a different form. Neither resolves Conjecture 3.
* The bridge is about ten lines combining a published theorem (Lew) with a classical theorem (Lovász–Kruskal–Katona), and its k = 2 case is the 2026 Kothari–Tudose theorem. This is the zero-credit "routine bridge from published lemmas / classical theorems" profile (precedents 345906, 351504, 359474, 371637). **No credit is claimed.** The MathDB item should be recorded as resolved by the literature (Lew 2025 + KK for k ≥ 3; Kothari–Tudose 2026 for k = 2).
* A numerical sanity check (diagnostic only; scripts/abebe_check.py; logs/abebe-check-r2.log, logs/abebe-check-r3.log) tested 150 random pure 2-complexes and 80 random pure 3-complexes on 7 vertices. Both Lew's bound and the derived bound hold (maximum excess 0, attained only in equality cases such as a single simplex at t = 1).
