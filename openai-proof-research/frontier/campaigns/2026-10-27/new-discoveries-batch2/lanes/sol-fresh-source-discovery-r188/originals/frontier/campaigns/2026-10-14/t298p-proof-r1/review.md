# T298P independent proof-correctness review, round 1

Role: independent proof correctness only. No contribution or novelty verdict, no count, no acceptance. The parent alone accepts.
Reviewer: Claude Opus 5.5, acting as review subagent. No nested agents were used. I did not open the parallel review directories (`t298p-contribution-r1/`, `t298p-parent/`) and drew no inference from them.

## Verdict

**PASS_FULL_T298P**, with three required attribution/explicitness repairs (R1–R3) and nine optional clarifications (O1–O9). None of the required repairs needs a new argument. Each asks the author to state or cite a result that is already true, where I verified the hypotheses myself. R1 uses a paid primary proposition (Shlyakhtenko, Proposition 3.2). R2 and R3 use classical theorems that the pinned source states as known. Every quantifier of the frozen target is established by the frozen argument together with these citations.

The frozen author packet should still be described as needing presentation revision before any manuscript. The verdict concerns the mathematics of the full unchanged target. It does not certify the packet's wording as manuscript-ready.

## 1. Target and anchors

The frozen target (`scope-freeze.md`, SHA256 `8e9b3f5f…589e`, unchanged) asks for exactly two bounded self-adjoint Z1, Z2 in a von Neumann algebra with a faithful normal tracial state, satisfying −∞ < χ(Z1,Z2) < χ*(Z1,Z2) < ∞. Here χ is the original cutoff, limsup-over-sizes microstates entropy with unnormalized Hilbert–Schmidt (HS) Lebesgue volume, and χ* is source298's normalization (eq. `chistar`, n = 2). The candidate proves a stronger transfer (1):

  liminf_{ε→0} [χ* − χ](E_ε(X)) ≥ g/k²,

for the source298 tuple X = V_h, with n = 2^64 + 1 = k² + 1 and k = 2^32.

Before reading, I ran the author's verifier from the author directory with the externally supplied anchor `b6c52528…beb3`:

- Positive run: PASS, with 20 payloads, 19 canonical blobs and 3 PDF/text pairs.
- An all-zero anchor was rejected with `FAIL: external manifest anchor`.
- Direct SHA256 of candidate.md, scope-freeze.md, comparison.md, matched-volume-attempt.md, unconditional-score-construction.md and stress-checks.md matched all six external anchors.

These checks authenticate identity only.

## 2. Re-derived argument and audit

Below, D = (diag(1..k), path or tree adjacency), V_a is a tr_k-orthonormal basis of the normal space, O_b is an orthonormal orbit basis, and N_alg = M_k(M).

### 2.1 Normal slice and coarse inverse (candidate §3; unconditional-score §1)

Re-derived by hand:

- **Kernel and normal space.** The kernel of H ↦ (i[H,D_1], i[H,D_2]) is R·I, because commuting with diag(1..k) forces diagonality and the tree edges equate diagonal entries. So the orbit rank is k² − 1 and the normal dimension is k² + 1. The normal space is characterized by Σ_s [D_s, V_as] = 0.
- **Coarse bimodule.** The coarse bimodule is M_k⊗M_k, with the left action on the first factor and the right action on the second. The M_k-central vectors are exactly span{w_bc}, with w_bc = Σ_i E_ib ⊗ E_ci, a space of dimension k².
- **Kernel of J.** J(η) = ([D_1,η], [D_2,η]) vanishes iff η commutes with alg(D_1, D_2) = M_k. So ker J = span{w_bc} and rank J = k⁴ − k².
- **Orthogonality.** J*W_{a,bc} = Σ_s [D_s, V_as] w_bc = 0.
- **Gram matrix.** ⟨W_{a,bc}, W_{e,fg}⟩ = δ_ae δ_bf δ_cg / k, by direct matrix-unit computation.
- **Invertibility.** The dimensions k²(k²+1) + (k⁴ − k²) = 2k⁴ add up, so F_0 = [W | J on (ker J)^⊥] is invertible. Tensoring with the coefficient algebra preserves this.
- **Well-defined derivations.** A value Σ_bc w_bc θ_{a,bc} with inner-leg coefficients θ ∈ A⊗A commutes with M_k⊗1. I checked: (E_lm⊗1)·Σ_i(E_ib⊗α)⊗(E_ci⊗β) = (E_lb⊗α)⊗(E_cm⊗β) = Σ_i(E_ib⊗α)⊗(E_ci⊗β)·(E_lm⊗1). So the derivations are well defined on the formal algebra M_k⊗C⟨u,t⟩, vanishing on M_k and on T.
- **Entry adjoint.** For Δ_{a,bc}(E_ij⊗p) = (E_ib⊗p_1)⊗(E_cj⊗p_2), the trace contraction is δ_ib δ_cj/k² · (τ⊗τ)(∂_a p). Pairing with E_cb ξ_a/k gives tr_k(E_cb E_ij)·τ(ξ_a p)/k, which is the same quantity. So the adjoint at 1⊗1 is E_cb ξ_a/k. This uses that ξ_a is a conjugate system for U relative to W*(T), which holds by freeness.
- **Inserted-coefficient adjoint.** For d(U_a) = α⊗β, I re-derived d*(1⊗1) = βξ_aα − β(τ⊗id)(∂_aα) − (id⊗τ)(∂_aβ)α. It comes from ∂_a(αPβ) and the relative conjugate identity on polynomials in U, T. The leading term is ξ multiplied by the coefficients, and the correction terms are contracted derivatives, as the candidate states.
- **Inner derivation.** (ad η)*(1⊗1) = (id⊗τ)η − (τ⊗id)η, in the orientation x⊗y ↦ τ(y)x − τ(x)y. It is bounded by 2‖η‖_proj, with no domain issue.
- **Perturbation structure.** Z_s is linear in U and the normal derivations vanish on T and M_k. So the only ε-perturbation of F_0 is ε[Y_s, ·] acting on η, where Y_s = Σ V_as⊗U_a + Σ O_bs⊗T_b. This is outer multiplication of the A⊗A coefficients, bounded in projective norm by C_k·R. The Neumann series converges for εC_kR‖F_0^{-1}‖ < 1/2. Each order-l summand has words of length ≤ l, so its difference-quotient cost is ≤ l, and the differentiated series converges.
- **Leading score.** The projection of (δ_js 1⊗1)_s onto span W is (1/k)Σ(V_aj)_cb W_{a,bc}. Hence Ξ_j^0 = (εk²)^{-1} Σ_a V_aj ⊗ ξ_a, and Σ_j ‖Ξ_j^0‖² = Φ*(U)/(ε²k⁴) by orthonormality of the V pairs.
- **Remainder.** The remainder is (1/ε)·O(ε)·(‖ξ‖ + 1) from the Neumann corrections, plus O(1) from η. This gives inequality (3).
- **Unconditional projection.** δ_j(Z_s) = δ_js 1⊗1, so δ_j(P(Z)) = (∂_jP)(Z) for every formal polynomial P. Hence E_{W*(Z)}[δ_j*(1⊗1)] is the **unconditional** conjugate variable. No relative-to-unconditional step is discarded. Algebraic freeness of (Z_1, Z_2) is never needed because everything is formal-then-evaluated.
- **Consistency.** As a sanity check, Φ*(D + σS) ≈ (k²+1)/(k²σ²) agrees with entropy-dimension 1 + 1/k² heuristics. It also respects the marginal lower bound Φ*(Z_1) + Φ*(Z_2) ≈ 2/(kσ²) and the relative upper bound 2/σ². Φ*(Z : M_k) contains the term (k² − 1)/u from T, whose time integral diverges. The inner derivations avoid exactly that term.

Numerical support (my own code, `checks/coarse_inverse.py`): for k = 2, 3, 4 with path and star trees, the Gram error is ≤ 2e-16, ‖J*W‖ ≤ 2e-16, rank J = k⁴ − k², F_0 is square and invertible, and the leading coefficient error is ≤ 1.5e-15. `checks/derivation_equation.py` solves the full equation exactly in a genuine finite coefficient algebra A = M_m (k = 2, m = 2 and 3, up to 2592 unknowns). At ε = 0 the normal coefficient is exactly (1/k)(V_aj)_cb(1⊗1). The normal and inner deviations scale linearly in ε (doubling ratios 1.98–1.999). These are finite diagnostics, not proofs.

### 2.2 Exact free-noise decomposition and the χ* increment (candidate §4, (4))

- **Decomposition.** S_pair = (1/k)Σ H_α⊗s_α over a tr_k-orthonormal pair basis. A real orthogonal change of basis to {V_a} ∪ {O_b} yields free semicirculars (S_a, R_b). At t = ε²k²u, √t/(εk) = √u exactly, so Z_ε + √t S_pair = D + εV(X + √u S) + εO(√u R). This is exact.
- **Freeness.** U(u) = X + √u S is free from T(u) = √u R. Φ*(U(u)) ≤ Φ*(X) ≤ n/h < ∞, with norms bounded uniformly for u ≤ U_0.
- **Increment.** χ*(Z+√T S) − χ*(Z) = ½∫_0^T Φ* follows from eq. `chistar`, because χ*(Z_ε) ≥ χ(Z_ε) > −∞ makes ∫_0^T Φ* finite and the tail term is O(T/M). Integrating (3) with dt = ε²k² du gives (4), with error C_{U_0} ε (1 + Φ*(X)).
- **What is not used.** No upper semicontinuity of Φ* and no hidden X. This is correct.

### 2.3 Global tube, injectivity and Jacobian (candidate §1; matched-volume A, F)

- **Operator-norm inverse.** The inverse of L_d is applied coefficientwise via partial traces against a fixed scalar inverse, so ‖L_d^{-1}‖_op ≤ C_k independent of d. The local injectivity estimate ‖L^{-1}(Φ(x) − Φ(y)) − (x − y)‖ ≤ ½‖x − y‖ holds on a uniform operator-norm ball.
- **Global uniqueness.** Suppose U(D+Y)U* = U′(D+Y′)U′*, and put W = U′*U. Then ‖[W, D_s⊗I]‖ ≤ 2r.
  - ([W, D_1])_ij = (j − i)W_ij, so the off-diagonal blocks are O(r).
  - On a tree edge (i,j), ([W, B])_ij = W_ii − W_jj + (off-diagonal terms), so all diagonal blocks are within O_k(r) of each other.
  - The polar part of the averaged diagonal block gives ‖W − I⊗g‖ = O_k(r). The group chart (K, g) ↦ exp(iK)(I⊗g) (Banach inverse function theorem, uniform in the algebra) and local injectivity then give [U,Y] = [U′,Y′].
  - The argument is valid in any coefficient C*/von Neumann algebra.
- **Jacobian.** dΨ_Y = dΨ_0 + E with ‖E‖_{HS→HS} ≤ 2‖Y‖ and dΨ_0dΨ_0* ≥ s² > 0 uniformly in d, so det-ratio ∈ (1 ± Cε)^{2k²d²}. The stabilizer-fibre factor in the coarea normalization changes by (1 + O(ε²))^{d²/2}. Together these give exp(±Cεd²).
- **Upper bound needs no injectivity.** The area/coarea formula gives Vol(image) ≤ ∫J / (fibre volume).

Numerical support (`checks/tube_geometry.py`, k = 2, 3, d = 1–6):

- Local-solver iteration counts are 7–10, independent of d. The orbit residual is ≤ 7e-15, and the normal remainder is ≤ 0.32ρ².
- |log Jacobian ratio| / (ρd²) ≤ 1.43, decreasing in d.
- dist(W, I⊗U(d)) / ‖[W, D]‖ ≤ 1.19, for W both near and far (Haar) from the stabilizer.

### 2.4 Matched volume formula (candidate §2, (2); matched-volume B, C, D, G)

**Constants.**
- The amplified orbit spectrum is the scalar spectrum of L repeated d² times, because Tr_kd-unit vectors (H⊗K)/√k have the same normalized ratio.
- The stabilizer metric factor is k^{d²/2}, the normal-fibre Jacobian is (ε√k)^{nd²}, and A_d = c_D^{d²} Vol U(kd) / (k^{d²/2} Vol U(d)).
- Vol U(l) = (2π)^{l(l+1)/2} / ∏_{j<l} j!. The first-column recursion (sphere metric ×2 in the 2l − 2 horizontal directions, ×1 for phase) checks out, and c = 3/4 + ½ log 2π.
- In the lower normalization, the log d coefficient is (1/k²)(−(k²−1)/2 − n/2) + 1 = 0 and the log k coefficient is (1/k²)(−(k²+1)/2 + n/2) + 1 = 1. So C_D = log k + ((k²−1)/k²)c + (log c_D)/k². The k = 1 check gives C_D = 0.

Numerical support (`checks/volume_normalization.py`):
- The recursion matches the product formula to 6e-13.
- (log Vol U(l) + ½ l² log l)/l² → 1.66893853…, which equals c.
- The exact log A_d minus the formula is 2e-8 · d² at d = 2000.
- The lower normalization converges to C_D (error 2–4e-9).
- The upper accounting at N = 2001 → 200001 shows no log N drift, and the excess falls from ≈2.2 to ≈0.27 as θ goes from 0.1 to 0.01.

**Lower bound.** The bundle over U(d)-invariant cutoff-R microstates maps injectively into the output microstate sets, since conjugation preserves all moments and the cutoff is R_out = ‖D‖ + εR Σ‖V_a‖. Any source subsequence d realizing the limsup gives output sizes kd. This is valid for the original limsup. See R1 for the cutoff used.

**Upper bound, every size N.** I re-derived the recovery lemma:

1. **Band ranks.** Band traces are exactly 1/k, by the norm-continuous homotopy D_1 + sεH_1 and the fact that projections at distance < 1 are equivalent. Microstate band ranks are N/k ± θN, by continuous cut-offs on actual spectral gaps.
2. **Tree-edge polar maps.** In the actual algebra, e_jZ_2e_iZ_2e_j ≈ e_j. Truncated polar maps on [½, 2] exclude only θN directions. The mass near the cut is controlled by ‖Q − f(Z_1)‖_2 and Hoffman–Wielandt, the same operation as source298 (block-outlier).
3. **Common root.** Pullbacks along tree paths lose at most the sum of the excluded ranks. The restricted path maps are exact isometries with orthogonal ranges, so they give exact matrix units on a corner of rank kd′.
4. **Moment convergence.** Moments of the pulled-back entries converge to those of the actual polar-coordinate entries ψ̂_i*Z_sψ̂_j in (e_rNe_r, kτ). Normalization is exact because τ(e_r) = 1/k.
5. **Second truncation.** For a good spectral subspace G_H of each Hermitian part H, ‖QHQ‖ ≤ ‖H|_{G_H}‖ for Q ≤ G_H. So the compressed pair is within C_k·a = O(ε) of D in operator norm, with rank loss still ≤ θN.
6. **Source law recovered.** The polar coordinates of the actual pair are Θ(Z) = (Ad ω)^{(k)}(Ω*ZΩ), with Ω ∈ U(N_alg) close to 1. The group chart writes Ω* = exp(iK_Ω)(I⊗g). So the local inverse returns normal coordinates gXg*, which carry the law of X. A uniformly convergent NC power series transfers this to the matrix compressions, so the recovered x′ ∈ Γ_{d′}(X; m′, δ′, R′) with R′ = O(1) independent of ε and of the output cutoff R.
7. **Volume bound.** The net cost is ≤ (C/η)^{2N(N−kd′)}. A near projection is intertwined by a unitary within Cη of 1, which moves the compressed pair by ≤ CRη. The complement ball has real dimension 2(N² − r²) and radius √(2N)R, and its log N terms cancel with the retained block. The total cost is C[θ log(C/θ) + θ log(C/η)].
8. **Order of limits.** Fix R, ε and (m′, δ′). Choose η (depending on R, ε, m′, δ′). Refine the output accuracy so θ → 0. Then take η → 0, then the infimum over (m′, δ′), then the supremum over R. Every retained d′ ≥ (1 − θ)N/k → ∞, so the source limsup bound at fixed (m′, δ′) applies to all of them, with no residue class dropped and no liminf introduced. The (d′/N)² prefactor contributes only O(θ)·|bracket|.

Numerical support (`checks/recovery_simulation.py`): source tuples are correlated and non-free; the encoding is hidden by a Haar unitary; low-rank outliers of size ≤ 3 are added; and N is not divisible by k.
- The clean model is recovered exactly (moment error ≤ 6e-14, zero rank loss).
- For k = 2, the rank loss is ≈ 50–60 at every N = 201, 401, 801, so the fraction falls 0.24 → 0.15 → 0.07. The max moment error falls 0.119 → 0.082 → 0.036.
- For k = 3 (N = 451 → 901), the fraction falls 0.36 → 0.17 and the moment error 0.185 → 0.089.
- The compressed pair is within the threshold of D in operator norm.

My first simulation calibrated the threshold on the original-coordinate deviation εVX. It discarded almost the whole root, because the polar-coordinate deviation also contains an O(ε) orbit component (see O1). That was a defect in my simulation, not in the candidate.

### 2.5 χ increment (candidate §4, (5); matched-volume E, F)

- **Straightening.** The fixed-point solver K = L^{-1}(P_o W + R(K, W)) is a strict contraction in the absolute NC-majorant norm on a radius ρ_0 fixed by k. With W = ε(VU + OT), the majorant radius in U is ≍ ρ_0/ε. Since P_o VU = 0, K_1 depends only on T, and H_ε(U,T) = U + εR_ε(U,T) is self-adjoint. The inverse G(h) = h − εR_ε(G(h), T) is another contraction, so F∘G = id holds by construction and G∘F = id by uniqueness of the fixed point. Both are formal identities with radii far exceeding ‖U‖.
- **Law identity.** exp(iK) ∈ U(M_k(W*(U,T))) conjugates the noisy pair exactly to E_ε(H_ε). Conjugation by a unitary of the ambient algebra preserves the joint law, so χ(noisy) = χ(E_ε(H_ε)).
- **Shlyakhtenko, under the stated hypotheses** (actual text read):
  - Thm 2.19 (U free from W*(T), W*(T) embeddable) gives χ(U|W*(T)) = χ(U), for the limsup χ. The case p = n has no limsup-of-a-sum issue, and W*(T) has microstates at all large sizes.
  - Thm 4.1 (F, G ∈ B[t], mutually inverse, ‖U‖ < min(r, R)) gives χ(H_ε|B) = χ(U|B) + Tr⊗τ⊗τ log|D_B F| with |log term| ≤ nCε, because ‖D_B F − I‖_proj ≤ Cε and the projective norm dominates the spatial norm.
  - The fixed-R fibre inclusion Γ_R(H|y) ⊂ Γ_R(H) gives χ_R(H) ≥ χ_R(H|B). Prop 3.2 gives χ_R(H|B) = χ(H|B) for R > ‖H‖ (see R1).
- **Conclusion.** The lower half of (2) at A = H_ε and cutoff R_1 = ‖U‖ + 1, together with the upper half at A = X, cancels the same C_D. This yields (5).
- **Only a microstates theorem is used.** No χ* change-of-variables is invoked.

### 2.6 Strictness and finiteness (candidate §5)

- gap(Z_ε) = gap(noisy) + Δχ − Δχ* ≥ k^{-2}[gap(X) − gap(X + √U_0 S)] − C_{U_0}ε, using χ ≤ χ* at the noisy pair (R2).
- The noisy source gap satisfies 0 ≤ gap ≤ (n/2) log(1 + C_X/U_0) → 0. The lower bound uses Shlyakhtenko Prop 4.2 (read: W*(X) embeddable ⇒ χ(X + √t S) ≥ (n/2) log 2πet). The upper bound is Voiculescu's χ* covariance bound with C_X = n^{-1}Σ τ(X_i²).
- Since gap(X) ≥ ½ (source Thm 1.1), choosing U_0 and then ε gives gap > 0. Finiteness: χ > −∞ by the lower half of (2), χ* ≥ χ, and χ* ≤ log(2πe·½Σ τ(Z_s²)) < ∞.

### Quantifier ledger

| Original quantifier | Where established | Status |
|---|---|---|
| ∃ M with faithful normal tracial state | M_k(W*(X)) with tr_k⊗τ (source 298 §4 realization) | established |
| exactly two bounded self-adjoint variables | Z_ε = E_ε(X) | established |
| χ original cutoff/limsup/unnormalized HS | used throughout; relative entropy only as an intermediate lower bound via fibre inclusion; no ultrafilter | established |
| χ > −∞ | lower half of (2) at X (any fixed R) | established |
| χ < χ* (strict) | (1) via (4), (5), BCG at the noisy pair, U_0 then ε | established (R1, R2 citations) |
| χ* < ∞ | covariance bound | established |
| n = k² + 1 matches the source tuple length | p = 2^64, k = 2^32 | established |

## 3. Required repairs (non-blocking for the verdict; mandatory for any manuscript)

**R1 — Cutoff uniformity in the lower half of (2) at the noisy endpoint.**
- finite-entropy-chart.md:57–70 proves χ(E_ε(A)) ≥ k^{-2}χ_R(A) + … for a fixed cutoff R, with ε small depending on R and an O(ε) constant proportional to R.
- candidate.md:37 (2) and matched-volume-attempt.md:100 ("Apply B to H_epsilon") replace χ_R by χ(A). For H_ε that replacement needs cutoff independence. Otherwise the cutoff realizing χ(H_ε) could depend on ε and spoil the uniform O(ε) term.
- Repair: apply the lower bound at the fixed cutoff R_1 = ‖X‖ + 2√U_0 + 1 > sup_ε ‖H_ε‖. Use χ_{R_1}(H_ε) ≥ χ_{R_1}(H_ε|W*(T)) (fixed-R fibre inclusion) and Shlyakhtenko Prop 3.2, χ_{R_1}(·|B) = χ(·|B) for ‖·‖ < R_1, before Thm 4.1 and Thm 2.19.
- Prop 3.2 is stated in the paid primary; its proof there is omitted and attributed to Voiculescu [4]. Its hypothesis holds here. The upper half needs no such step.

**R2 — Attribution of χ ≤ χ* at the noisy pair.**
- The strictness step (candidate.md:118) and the finiteness claims use the general comparison χ ≤ χ*. The packet calls it "the source-stated comparison".
- Source298 states it only in its introduction, as Biane–Capitaine–Guionnet [BCG] and Jekel–Pi [JP]. It is not a theorem proved there.
- A manuscript must cite and quote the BCG/JP statement (all bounded self-adjoint tuples, limsup χ). Neither the author nor I read those primaries; see the reading limits.

**R3 — Attribution of the classical free-probability inputs that make §4 "exact".** State and cite:
- (a) (1/k)Σ H_α⊗s_α, with s_α free from M, is a standard semicircular pair free from all of M_k(M), not only from M_k. This follows from operator-valued semicircularity over M_k with scalar covariance η(m) = tr_k(m)1.
- (b) Conjugate variables of U are conjugate relative to W*(T) when U and T are free.
- (c) Φ*(X + √u S) ≤ Φ*(X).
- (d) Voiculescu's χ* ≤ (n/2) log(2πe·mean variance).

These are classical and true as used, but the packet uses them without citation.

## 4. Optional clarifications

- **O1.** In C.4 and candidate.md:65, "actual O(ε) norm" should say explicitly that the threshold is measured in the polar coordinates of the actual algebra. Their deviation from D includes an O(ε) orbit component, not only εVX. The text says "these root entries", which is correct, but my first simulation misread it.
- **O2.** Replace "triangular shear of determinant one" (matched-volume-attempt.md:23) with the actual argument: the perturbation bound on dΨ_Y relative to dΨ_0, plus the (1 + O(ε²))^{d²/2} stabilizer-fibre factor in the coarea normalization. Note also that the upper bound uses the area formula without injectivity.
- **O3.** Write out the discontinuous-truncation step in C.2–C.3: the ‖Q − f(Z_1)‖_2 estimate, Hoffman–Wielandt for the squared singular-value operator, and the mass of the microstate spectrum near the cuts. This is the same operation as source298's (block-outlier).
- **O4.** State that the derivations are defined on the formal algebra M_k⊗C⟨u,t⟩ and then evaluated, so no algebraic freeness of (Z_1, Z_2) or of (U, T) is needed.
- **O5.** Shlyakhtenko's B[t] notation writes one elementary coefficient tensor per index pattern. State that sums are allowed and that the absolute NC majorant dominates the majorant F̂ used for the multiradius.
- **O6.** The net size η must be chosen after the output cutoff R as well as after ε and (m′, δ′), because the net relaxation is CRη. G.5 omits R.
- **O7.** "o(N)" at fixed microstate accuracy should read "≤ θN with θ → 0 as accuracy refines". G.5 already does this.
- **O8.** The global "almost commuting ⇒ near stabilizer" step is needed only for the lower-bound injectivity. In the recovery, the polar-coordinate identification needs only the group chart near 1 for Ω*.
- **O9.** Only the lower half of (2) at H_ε (noisy endpoint) and the upper half at X are used. It would help to present (2) as two one-sided lemmas with their exact hypotheses: norm bound, fixed cutoff, ε range.

## 5. Checks and seal

All scripts are new reviewer code, run with `/var/tmp/r99-eval-env/bin/python -I` (NumPy 2.5.4, cached, nothing installed). Their outputs are in `checks/outputs/`. They support finite algebra, normalizations and the recovery construction only. They prove no free-probability or entropy statement.

| Script | What it checks | Result |
|---|---|---|
| `coarse_inverse.py` | normal slice, Gram 1/k, J*W = 0, rank/kernel of J, F_0 invertibility, leading coefficient, matrix-unit contraction, score-norm identity (k = 2, 3, 4; path/star trees) | pass |
| `derivation_equation.py` | full derivation equation in A = M_m; ε-linear deviations | pass |
| `volume_normalization.py` | Vol U(l), c, c_D multiplicity, A_d, C_D, rank-loss accounting | pass |
| `tube_geometry.py` | uniform local solver, Jacobian ratio, almost-commuting constant | pass |
| `recovery_simulation.py` | full arbitrary-size recovery with outliers and N ∤ k | pass (deterministic; rerun byte-identical) |

The seal (`MANIFEST.json`, read-only `verify.py`, copied controls) is described in `seal-and-controls.md`. The manifest SHA256 is reported externally by the reviewer, not inside this packet.

Reading limits: `reading-limits.json`.
