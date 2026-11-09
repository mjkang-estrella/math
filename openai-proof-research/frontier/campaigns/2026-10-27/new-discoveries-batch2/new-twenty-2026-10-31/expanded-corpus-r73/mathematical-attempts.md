# r73 mathematical attempts

Lane: expanded-corpus-r73, MathDB IDs 377968–379120 (40 IDs). All entries carry zero credit; root acceptance is separate.

## Route 1 (sustained, closed): 378395, the collapsing conjecture for hierarchical-model facets

Source: Eriksson–Fienberg–Rinaldo–Sullivant, arXiv:math/0405044, Section 4. For Δ = [12][13][23], P_Δ^{p,q,r} is the cone over the pqr columns col(i,j,k) = e^{12}_{ij} + e^{13}_{ik} + e^{23}_{jk}. Conjecture: for p ≤ q ≤ r, every facet of P^{p,q,r} is obtained by collapsing from a facet of P^{p,q,q}. The source checked this only up to 4 × 4 × 4 (Table 1).

**Mechanism.**
- A facet inequality is a = (a_ij), b = (b_ik), c = (c_jk) with a_ij + b_ik + c_jk ≥ 0 on all cells, extreme modulo lineality.
- For fixed a, slice k contributes (u, v) = (b_{·k}, c_{·k}) ∈ Q(a) = {u_i + v_j ≥ −a_ij}. If a slice were not a vertex of Q(a) modulo the shift, perturbing that slice alone would contradict extremality. The only exception is a ≡ 0, which gives the [13]/[23] margin facets.
- Q(a) is dual to the regular subdivision of Δ_{p−1} × Δ_{q−1} with heights a. Extremality means the subdivision is coarsest: dim L(a) = p + q, where L(a) consists of the heights a′ that are potentials on every cell.
- The largest number of pairwise distinct slice patterns equals the number of maximal cells. Collapsing slices merges identical patterns, so a facet with more than q distinct slices cannot come from P^{p,q,q}.

**Search.** `scripts/coarse.py` enumerates all spanning trees of K_{p,q} to find the vertices of Q(a), and uses a modular rank for dim L(a). A modular rank is only an upper bound on the true dimension; every reported hit was re-certified in exact arithmetic.

| Grid | Height range | Configurations | Rays found, by cell count |
| --- | --- | --- | --- |
| 2 × 3 | 0..2 | 9 | 2 cells only |
| 3 × 3 | 0..2 | 81 | at most 3 cells |
| 3 × 3 | 0..3 | 256 | at most 3 cells |
| 3 × 4 | 0..2 | 729 | at most 4 cells |
| 3 × 4 | 0..3 | 4096 | at most 4 cells |
| 3 × 5 | 0..1 | 256 | at most 4 cells |
| 4 × 4 | 0..1 | 512 | 2 (49), 3 (144), 4 (144), **5 (54)**, **7 (6)** |

The p < q and 3 × 3 cases agree with the source's table. In the 4 × 4 case, all 60 rays with more than 4 cells were certified exactly by `scripts/facet_cert.py` (`outputs/collapsing-444r-certificates.json`): the inequality is valid, the tight columns have rank dim − 1, and the slice patterns are pairwise distinct. They are facets of P^{4,4,5} (54 examples) and P^{4,4,7} (6 examples), the latter including the symmetric a_ij = [i ≠ 0, j ≠ 0, i ≠ j].

**Proof and Lean.** The ordinary proof is in `lean-packet/PROOF.md`. The literal Lean endpoint is `¬ CollapsingConjecture`; the integer certificates (43 biorthogonal functionals, 12 margin relations, c₀ = (0,0,0)) are checked by `decide +kernel`, and rank–nullity gives the dimensions 44 and 43. The fresh extracted replay passes (`lean-packet/fresh-replay-receipts/result.json`).

Remaining: independent statement-fidelity and significance review, and root decision. Bounded searches found no prior refutation (`outputs/web-searches.json`). Global novelty is not claimed.

## Route 2 (sustained, parked): 378740, minimal Hilbert function of double points on C_{t,r}

**Status.** The source is Geramita–Migliore–Sabourin, arXiv:math/0411445. Later work (arXiv:1109.3610) proves the minimum for s ≤ 9 and s = 11, so the first open literal cases are t = 5, r = 2, 3, 4 (s = 12, 13, 14) and t ≥ 6.

**Method.** h_{2X}(d) is the rank of the value and first-derivative conditions on forms of degree d; in degree ≥ 1, the three partials suffice by Euler's formula. Screening uses ranks modulo 2³¹ − 1. Because rank mod p ≤ rank over Q, any configuration whose modular values are all ≥ the reference is certified, and only candidates would need exact recheck. None arose.

**References.** The Z_{5,r} references reproduce the source table exactly. The Z_{6,r} references were computed from two independent C_{6,r} realizations, which agree.

**Coverage.**
- Affine grids (`bin/dbl`): all N-subsets of the 4 × 4 grid for t = 4, r = 1–3 and t = 5, r = 1–4, and of the 5 × 5 grid for t = 4, r = 1. That is 523,318 subsets, with no violation.
- Projective line-arrangement pools (`bin/dbl2`, batches A–E): K = 6–8 lines, coefficient boxes 2–3, some pools with 3 extra random points. That is 443 pool runs, 895,245 subsets and 698,254 generic supports, with zero candidates. Generic supports by case: (5,2) 372,613; (5,3) 136,579; (5,4) 106,987; (6,1) 60,922; (6,2) 16,881; (6,3) 3,710; (6,4) 518; (6,5) 44.

**Remaining.** A Geramita–Hà-style case analysis for s = 12–14. Lean formalization of fat-point Hilbert functions is not feasible in this pass. Parked.

## Route 3 (sustained, closed as known): 378584 and 378902

**378584.**
- Exhaustive lexicographic DFS with pruning on the partial collinear-triple count. A count exceeding (n − 1)/2 can never decrease, so the first complete hit is the lexicographic minimum.
- Coverage: primes n = 3, 5, 7, 11, 13, 17 in single runs, and n = 19 split over σ(3) ∈ 3..11. The answer equals g every time.
- The result was then found proved: Cooper–Hyatt, arXiv:2501.02331, Theorem `thm:lexleast` (body read).

**378902.**
- Search of multisets over Z_n using the equivalence 0 ∈ Σ_n(S) ⟺ σ(S) ∈ Σ_k(S) and translation normalisation. The code was validated against itertools brute force, with matching positive counts 2, 4, 2, 26, 84.
- Coverage: no counterexample for n ≤ 12 and all k, nor at the n = 14 and n = 15 boundary values. The known sub-range counterexample at n = 15, k = 3 is detected.
- Cao (EJC 2006) settles n with two prime divisors. The general case is DeVos–Goddyn–Mohar Corollary 1.8, which implies GTZ Conjecture 1.7(1) (proof body read). The general argument reduces to DGM's subsequence-sum version of Kneser's theorem plus Gao's Lemma 2.

## Other mechanisms checked

**377968 (stable torsion length).** Dihedral argument: if f = st with s² = t² = 1, then f^n = s · (s f^n) and s f^n is an involution, so τ(f^n) ≤ 2 and ||f||_τ = 0. In Mod_g, ι · (t_b ι t_b^{-1}) = t_{ι(b)} t_b^{-1} has infinite order when ι(b) is disjoint from and not isotopic to b. This is already in Kotschick, arXiv:math/0307362 (Example `ex:involutions`). Mathlib has no mapping class groups, so Lean is infeasible regardless.

**379012 (multiplicity bound for torsion modules).**
- The literal statement fails for N = (R/(x₁))²: e = 2 > (M₁ − m₀)/1! = 1. The source's own codimension-1 theorem fails on the same module.
- This is a missing β₀ factor, an obvious formulation defect produced by direct-sum padding, so it is not credited.
- The corrected inequality is Boij–Söderberg's Theorem `thm:MultConj`.

**378162 (Borcea's twisted root maps).**
- Degree 2 holds outright for T = (1 − λD)e^{λD}: the root difference satisfies d² = Δ + 4λ² with Re d · Im d fixed, so the real spread increases and the imaginary spread decreases.
- An 80,000-test floating-point scan (n = 3–6, the operators (1 − λD)e^{λD} and e^{−aD²}) found no failure. This is a diagnostic only.

**378663, 378069.** Both are refuted in their own sources: Kellner's exceptions for 378663, and Hoffmann's "holds precisely up to rank eight" for 378069.
