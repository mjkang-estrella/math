# T298P independent proof-correctness review, round 2 (takeover)

Reviewer: round-2 takeover after the round-1 reviewer stopped on a rate limit without a verdict. This is a proof-correctness review only. It gives no contribution, novelty, attribution, acceptance or count verdict. The round-1 check code was inspected but not reused; the contribution and attribution review directories were not read.

## Verdict

**PASS_FULL_T298P**

The frozen full target is proved by the packet's argument: there exist exactly two bounded self-adjoint elements Z_1,Z_2 of a tracial von Neumann algebra (M_k(M), tr_k ⊗ τ) with

 -∞ < χ(Z_1,Z_2) < χ*(Z_1,Z_2) < ∞,

where χ is the original operator-norm-cutoff, limsup-over-matrix-sizes microstates entropy with unnormalized Hilbert-Schmidt Lebesgue measure. No ultrafilter, no liminf, and no conditioning on scalar matrix units replaces it.

There are no REQUIRED blocking gaps. Every step was re-derived independently. In a few places the packet states a routine step tersely; the completions the reviewer supplied are listed explicitly in each section ("reviewer completion") so the parent can see which details are written in the packet and which were filled in here. None of them changes a statement, a constant that matters, or the order of limits. Optional repairs are listed at the end.

The verdict is conditional only on (i) the pinned source298 theorem, accepted per AGENTS.md, and (ii) the classical published interfaces listed in "Classical interfaces". In particular Shlyakhtenko's Theorem 4.1 is a published theorem whose proof is omitted in the read arXiv v1; it is accepted as a classical interface, and its hypotheses were checked literally.

Reviewed packet: `frontier/campaigns/2026-10-14/fresh-structural-discovery-r104/`, external manifest anchor `b6c525288bd6a7203d13c8b8ed4b696e14a0f8c3a06cd30cb6fbe871d6dfbeb3`. The author verifier passes with that anchor; 8 copied-tree controls behave as expected (see "Integrity").

## Target and input

- Target (scope-freeze.md, candidate.md lines 7-11): as displayed above.
- Input (source298 01-introduction.tex line 47 and 04-signal.tex): a bounded n-tuple X = C + √h S, h > 0, n = 2^64 + 1, with -∞ < χ(X) ≤ χ*(X) − 1/2 < ∞, bounded matrix models (so W*(X) is embeddable), and Φ*(X) ≤ n/h < ∞ because S is a free semicircular family free from C.
- k = 2^32, so n = k² + 1, the exact dimension of the normal slice.

## Proof chain and audit

### 1. Encoding and coarse finite algebra (normal-slice-construction.md; candidate.md §1, §3)

Claims: D_1 = diag(1,…,k), D_2 = tree adjacency have scalar commutant; L(H) = (i[H,D_1], i[H,D_2]) has real rank k²−1; the orthogonal complement V of its range has dimension k²+1; at size kd the orbit tangent and V ⊗ M_d^sa are orthogonal and fill the pair space. In the coarse bimodule, w_bc = Σ_i E_ib ⊗ E_ci span the scalar-central subspace, the vectors W_a,bc have Gram matrix δ/k, J*W = 0, rank J = k⁴−k², and the leading normal coefficient of the target (δ_js 1⊗1)_s is (V_aj)_cb/k.

Audit: re-derived by hand and checked in floating point for k = 2, 3 (`checks/finite_geometry.json`, section `coarse`): Gram error ≤ 1.2e-16, rank J matches, J*W ≈ 1e-16, kernel equals span w_bc, the full coarse inverse has least singular value exactly 1/k, leading-coefficient error ≤ 6e-17. Status: correct.

### 2. Uniform global normal tube and its Jacobian (finite-entropy-chart.md; matched-volume-attempt.md A, F; candidate.md §1)

Claims: the map [U,Y] ↦ U(D ⊗ 1 + Y)U* on the associated bundle U(kd) ×_{I_k⊗U(d)} (V ⊗ M_d^sa) is injective on an operator-norm tube of radius independent of d, has a convergent noncommutative power-series inverse on a strictly larger radius, and has volume Jacobian exp(±Cεd²) relative to base-orbit volume times Euclidean fiber volume when ||Y|| ≤ C_R ε.

Audit.
- Local chart: the linear map L_d(K,Y) = i[K,D] + Y is the fixed k-level map tensored with the identity on M_d^sa, so both its Hilbert-Schmidt inverse and its operator-norm inverse (by finite block extraction) are bounded independently of d. The exponential-series derivative estimates are dimension-free. Segment integration gives injectivity. Correct.
- Analytic inverse (matched-volume-attempt.md F, lines 116-133): the equation K = L⁻¹P_oW + L⁻¹R(K,W) is a contraction in the absolute nc-power-series majorant norm; the fixed point is a convergent series with a radius margin. P_o is the finite orthogonal projection onto the orbit tangent, whose kernel is exactly V ⊗ A. Correct.
- Global uniqueness (lines 21, 29): if two representations agree, the transition unitary U satisfies ||[U,D_s]|| ≤ 2r. Then (i−j)U_ij = [U,D_1]_ij gives ||U_ij|| ≤ 2r for i ≠ j, the tree edges give ||U_ii − U_jj|| = O_k(r), and the polar part of the averaged diagonal block gives U = exp(iK)(I_k ⊗ V) with ||K|| = O_k(r). This reduces to the local chart. The argument uses only finite coefficient estimates, so it holds in M_k(A) for any tracial A, not just matrices; this is needed in §4. Supported by `checks/finite_geometry.json` section `almost_commute` (distance/commutator ≤ 0.77 over random trials, k = 2, 3, 4). Correct.
- Jacobian. Reviewer completion: at a bundle point [U,Y], use local coordinates (κ,y) ↦ U exp(iκ)(D+Y+y)exp(−iκ)U*, κ ∈ K_d. The bundle measure in these coordinates has density |det L_orbit| times Lebesgue, by U(kd)-invariance, so the Jacobian relative to (orbit volume × fiber Lebesgue) is |det(L+E)|/|det L| with E(κ,y) = i[κ,Y]. Since ||E||_{HS→HS} ≤ 2||Y||·||L⁻¹|| = O(ε), this ratio lies in exp(±Cε·2k²d²). This replaces the packet's "triangular shear" phrase (matched-volume-attempt.md line 23) by a direct computation; the conclusion is the same.
- Base-orbit volume A_d = c_D^{d²} Vol U(kd)/(k^{d²/2} Vol U(d)). The k^{d²/2} is the Hilbert-Schmidt scaling of I_k ⊗ U(d) inside U(kd), and c_D^{d²} is the product of horizontal singular values (each scalar singular value with multiplicity d²; the ratio is independent of trace normalization). The asymptotic in candidate.md lines 47-49 was checked numerically from the exact product formula Vol U(l) = (2π)^{l(l+1)/2}/∏_{j<l} j!: normalized residuals 2e-4, 1.5e-5, 1.1e-6, 8e-8 at l = 50…3200 for U(l), and 9e-6, 5.7e-7, 3.6e-8 at d = 100, 400, 1600 for A_d (without c_D). Only the fact that the SAME A_d appears in both halves of (MV) is used later, so even the exact value of C_D is immaterial. Status: correct.

### 3. Lower half of (MV) (matched-volume-attempt.md B; finite-entropy-chart.md)

Claim: Vol Γ_{kd}(E_ε(X)) ≥ A_d (ε√k)^{nd²} Vol Γ_d(X) exp(−Cεd²), giving χ(E_ε(A)) ≥ k⁻²χ(A) + (n/k²)log ε + C_D − Cε for every bounded A with finite χ.

Audit: Γ_d(X) is invariant under simultaneous U(d) conjugation, so the bundle over it is well defined. Conjugation preserves all normalized trace words, so the injective image lies in each output microstate neighbourhood for a suitable source neighbourhood. The coefficient map x ↦ εΣV_a ⊗ x_a has Jacobian (ε√k)^{nd²} because V is orthonormal for tr_k and volume uses Tr_{kd}. Every source subsequence realizing the limsup gives output sizes kd, so no liminf or ultrafilter enters. Bookkeeping (re-done): the log d terms total −k²d² log d = −r² log r + r² log k with r = kd, cancelling the output normalization log r; the (k²+1)/2 · log k terms from A_d and from (√k)^{nd²} cancel; dividing by r² leaves C_D = log k + ((k²−1)/k²)c + (log c_D)/k². Status: correct.

### 4. Uniform recovery lemma (matched-volume-attempt.md C, G.1-G.2; candidate.md lines 61-65)

This was the step singled out for scrutiny. Claim: for fixed small ε, any θ > 0 and any source neighbourhood, all sufficiently accurate bounded microstates Z of E_ε(X) in any size N have a projection P of rank kd ≥ (1−θ)N carrying exact matrix units such that PZP lies in the normal tube and its recovered coefficients lie in the prescribed source neighbourhood with a cutoff R' independent of N and θ.

Audit, step by step.
- Bands (C.1): the actual spectrum of Z_1 is within O(ε) of {1,…,k}. Portmanteau applied to the empirical spectral law gives o(N) eigenvalues in the closed gaps, so spectral projections differ from continuous functions g_i(Z_1) by rank o(N). The actual band projections are norm-continuous along D_1 + sεH_1 and hence unitarily equivalent to E_ii ⊗ 1 even if M is not a factor (candidate.md line 63). Correct.
- Truncated polar maps (C.2, G.2): the actual tree-edge compressions have singular values in a fixed interval; the truncated polar part Y·f(Y*Y) differs from Y·g(Y*Y), g continuous, on a spectral subspace of rank o(N). Pulling good domains back along the finitely many tree paths and intersecting loses at most the sum of the excluded ranks. The restricted path maps are isometries into orthogonal bands, so the matrix units are exact. No inverse on small singular values occurs. Correct.
- Moment transfer through a non-functional-calculus intersection (C.3). The earlier concern was that the root intersection is not a functional calculus of one operator. It does not need to be. Reviewer completion (the elementary rank lemma behind C.3, stated in the packet without proof): if bounded matrices with norm ≤ R' differ by a matrix of rank ≤ m, then every normalized trace word of length L changes by at most 2L R'^{L} m/N. Every compression used differs from the corresponding continuous-function expression by rank o(N). So the pulled-back root entries have joint moments converging to those of the actual polar-coordinate entries. Correct.
- Second truncation (C.4, G.1): for each Hermitian part h of a root entry minus its D-entry, with actual norm ≤ a, Portmanteau gives o(N) eigenvalues of the matrix h outside [−2a, 2a]. With Q ≤ 1_{[−2a,2a]}(h), ||QhQ|| ≤ 2a without invariance of Q. Recompression changes moments by o(1) by the rank lemma. Each compressed entry deviation then has norm ≤ 4a (real and imaginary parts), so each coordinate of the compressed pair is within 4k²a = O(ε) of D in operator norm. The finite simulation (`recovery`, k = 2, 3, N ≢ 0 mod k, junk rank inserted) stayed within the bound 4k²a, kept the matrix units exact (isometry error ≤ 6e-15), and reproduced the source moments exactly when no junk was inserted. Correct.
- Inverse and identification (C.5). In the actual algebra, the polar-coordinate pair Z' equals u E_ε(X) u* for a unitary u in M_k(M) that almost commutes with D. By §2 (valid in M_k(M)), u = exp(iK)(I_k ⊗ v), and uniqueness of the contraction fixed point gives recovered coefficients vXv*, which have the law of X. The tube inverse is a series that converges absolutely on a fixed operator-norm ball containing both the matrix entries and the actual entries. Uniform polynomial approximation therefore transfers moment convergence. The recovered cutoff is R' = C_k · (threshold)/ε = C'_k(||X||+1), independent of N, θ and the output cutoff. Correct.
- Uniformity. Reviewer completion: the packet argues along convergent sequences. The uniform statement ("there exist output parameters (m, γ) and N_0 such that every microstate…") follows by the standard contradiction argument: otherwise choose bad microstates with m_j → ∞, γ_j → 0, N_j → ∞, whose moments converge to those of E_ε(X), contradicting the sequential statement. Correct.

Status: correct. The earlier pre-review concern (moment transfer after the second truncation) is resolved by the rank lemma; no measurable selection is needed (see §5).

### 5. Upper half of (MV): covering and volume accounting (matched-volume-attempt.md D, G.3-G.5; candidate.md line 67-71)

Audit.
- Covering instead of a measurable map: each microstate's recovered P of rank r = kd is within η of a net projection Q, and the polar part W of QP + (1−Q)(1−P) is a unitary within Cη of 1 with WPW* = Q. Then QZQ, in the transported matrix units, is within C R_out η of PZP, so it lies in the tube over a source neighbourhood relaxed by O_ε(η). The tube image is U(r)-invariant, so the choice of frame for range Q is irrelevant. Correct.
- Volumes: for fixed Q, Lebesgue measure on pairs factors orthogonally into the r×r corner and the remaining real dimension M = 2(N²−r²), with the induced metric on cross blocks. The upper bound for the tube image needs only the area formula (no injectivity): Vol(Tube(Γ')) ≤ A_d (ε√k)^{nd²} Vol Γ'_d e^{Cεd²}, valid because ||Y|| ≤ εC R' is inside the Jacobian radius. The remaining blocks lie in a Euclidean ball of radius R_out√(2N) in dimension M, with log volume ≤ −(N²−r²) log N + C(N²−r²)[1 + log R_out + log(N²/(N²−r²))]. The net costs 2Nl log(C/η) with l = N − r, and ranks cost log(N+1). Re-derived: the log terms combine to −r² log r − (N²−r²) log N + N² log N = r² log(N/r) ≤ N² log(1/(1−θ)). After division by N² everything except the main term is O(θ log(C/θ) + θ log(C/η)). The main term carries the same C_D as §3.
- Source limsup: for fixed source parameters, limsup over d gives an upper bound valid for every large d, and every retained d ≥ (1−θ)N/k tends to infinity, so no residue class of N is dropped. χ_{R'}(X) = χ(X) for R' > ||X||.
- Order of limits (G.5): for fixed ε, source parameters and R_out, choose η for the relaxed accuracy, then output accuracy so that θ is small, then N → ∞, θ → 0, η → 0, source tolerance → 0, then sup over R_out. Consistent.

Status: correct. Equation (2)/(MV) holds with the same C_D on both sides and error O_{k,R}(ε).

### 6. Unconditional Fisher bound (3) (unconditional-score-construction.md §§1-3; candidate.md §3)

Claim: for U with finite conjugates, free from a bounded orbital tuple T, and Z = D + ε(VU + OT), Φ*(Z) ≤ Φ*(U)/(ε²k⁴) + C_{k,R} ε⁻¹ (1+Φ*(U)).

Audit.
- Well-definedness: the conjugate system ξ of U is also a conjugate system relative to W*(T) by freeness. The adjoint formula ∂*(a⊗b) = aξb − (id⊗τ)(∂a)b − a(τ⊗id)(∂b) shows that ∂_{U:T} is well defined on the represented algebra: if P(U,T) = 0, then ∂P pairs to zero with a dense set. The amplified entry derivations Δ_{a,bc} with value w_bc are therefore well defined. Correct.
- Inner-leg coefficient insertion and adjoints: checked in exact rational arithmetic with free semicircular test variables, including the Leibniz rule, centrality of w_bc, the matrix contraction (1/k)(E_cb ⊗ Ξ), and two negative controls (transposed matrix unit; dropped correction term), both detected (`checks/exact_adjoint.json`, k = 2, 3).
- Neumann series: the map (εc, η) ↦ values on Z is the fixed coarse isomorphism L_0 of §1 (tensored with A⊗A) plus ε times commutation with the bounded perturbation. So c − c⁰ = O(ε)/ε = O(1), η = O(1), and the differentiated series converges with an O(1) bound. The adjoint of ad(η) at 1⊗1 has L² norm ≤ 2||η||_proj.
- Leading term: Ξ⁰_j = (εk²)⁻¹ Σ_a V_aj ⊗ ξ_a and Σ_j ||Ξ⁰_j||² = Σ_{a,a'} δ_{aa'} τ(ξ_a ξ_a') = Φ*(U) exactly, by orthonormality of V (cross terms vanish through the V-orthonormality, not through ξ). Squaring (||Ξ⁰|| + C(1+√Φ))² and projecting onto L²(W*(Z)) gives (3).
- The composed derivation agrees with the free difference quotient on polynomials in Z because both are derivations with the same generator values.

Status: correct.

### 7. Exact free-noise decomposition and the nonmicrostates increment (4) (unconditional-score-construction.md §4; candidate.md §4)

Audit: a standard semicircular pair free from M_k(M) is realized by (1/k)Σ_m B_m ⊗ s_m over an orthonormal Hermitian pair basis (B_m), with s_m free standard semicirculars free from M. This uses the classical fact that a self-adjoint matrix with free circular/semicircular entries is semicircular and free from M_k(A_0). The coefficient covariance was checked exactly for k = 2, 3, 4 (`noise`). Orthogonal rotation into V and O keeps a free semicircular family, so at t = ε²k²u the noisy pair is exactly D + ε(V U(u) + O T(u)) with U(u) = X + √u S_n free from T(u) = √u S_o. The heat-flow definition gives χ*(Y_{t_0}) − χ*(Y) = ½∫_0^{t_0} Φ*(Y_s) ds (re-derived: the n/(1+s) terms cancel exactly). Substituting s = ε²k²u, with Φ*(U(u)) ≤ Φ*(X) and norms bounded for u ≤ U_0, gives (4) with error C_{U_0} ε(1 + Φ*(X)). Status: correct.

### 8. Analytic straightening and the relative change of variables, giving (5) (matched-volume-attempt.md E, F; candidate.md lines 105-112)

Audit.
- Straightening: with W = ε(VU + OT), the §2 solver gives K = O(ε) and exp(−iK) Z_noisy exp(iK) = D + εV H, where H = H_ε(U,T) = U + εR_ε(U,T). Unitary conjugation inside M_k(W*(U,T)) preserves the joint law (traciality), so χ(Z_noisy) = χ(E_ε(H)).
- Theorem 4.1 hypotheses, checked literally against shlyakhtenko-relative.txt lines 429-479. Reviewer completion on the presentation:
  - Take B = the unital algebra generated by T.
  - Grouping consecutive T-letters of each (U,T)-monomial gives a B[t] representation whose majorant F̂ is dominated by the (U,T)-majorant evaluated at T-radius ||T||. The multiradius therefore strictly exceeds ||U||.
  - The inverse G is the fixed point of A = H − εR_ε(A,T), computed in the Banach algebra of majorant-convergent series in the letters (H,T). Hence F∘G = id and G∘F = id hold as series identities, with a radius margin covering both ||U|| and ||H||.
  - Both F and G preserve self-adjointness because the solver works in the self-adjoint part, V is a real Hermitian basis, and the partial trace (tr_k ⊗ id)(V_as Y_s) of Hermitian inputs is self-adjoint.
  - Jacobian: D_B F = I + O(ε) in M_n(M ⊗̄ M^op), so |Tr ⊗ τ ⊗ τ (log|D_B F|)| ≤ C n ε with n fixed.
- Theorem 2.19 (lines 290-296): U is free from W*(T), and W*(T) is embeddable (semicircular), so χ(U|B) = χ(U).
- χ(H) ≥ χ(H|B): use Proposition 2.8 (χ(H|Y) ≤ χ(H : Y)) and the inclusion Γ(H : Y) ⊂ Γ(H). This avoids the "left to the reader" equality in Proposition 2.12, which is therefore not needed.
- Hence χ(H) ≥ χ(U) − C_{U_0} ε, which is finite. The lower half of (MV) applied to H (bound ||X|| + 2√U_0 + 1, ε below a U_0-dependent threshold) and the upper half applied to X give (5) after the identical C_D cancels.

Status: correct.

### 9. Strictness, finiteness and quantifier order (candidate.md §5)

Audit: by χ ≤ χ* (Biane-Capitaine-Guionnet, source298 01-introduction.tex lines 28-29) for the noisy pair, (4) and (5) give

 gap(Z_ε) ≥ k⁻²[g − gap(X + √U_0 S)] − C_{U_0} ε, g = χ*(X) − χ(X) ≥ 1/2.

For large U_0, χ(X+√U_0 S) ≥ (n/2) log(2πeU_0). This is the proof constant of Shlyakhtenko Proposition 4.2 (line 493); the printed statement at line 487 has the typo "n log", which the candidate does not use. It needs embeddability of W*(X), which holds by the bounded matrix models. Also χ* ≤ (n/2) log(2πe(U_0 + C_X)) by the covariance bound, so the noisy source gap tends to 0. Order: choose U_0 with gap(X+√U_0 S) < g/2, then ε small. Then gap(Z_ε) > 0, χ(Z_ε) > −∞ by (MV) or finite-entropy-chart.md, and χ*(Z_ε) < ∞ by the bounded-covariance bound. Then (1), liminf_{ε→0} gap ≥ g/k², also follows by letting U_0 → ∞. The pair lives in the tracial algebra (M_k(M), tr_k ⊗ τ) and consists of exactly two bounded self-adjoint elements. Status: correct; all quantifiers of the frozen target are met.

## Classical interfaces relied on (accepted, not audited)

1. Source298 main theorem and stated properties of X (pinned; accepted per AGENTS.md).
2. χ ≤ χ* (Biane-Capitaine-Guionnet), as stated in source298.
3. Voiculescu: cutoff independence χ_R = χ for R > ||X||; Φ*(X + free Y) ≤ Φ*(X); the heat-flow definition of χ* and the covariance upper bound; the Lebesgue-volume product formula for U(l).
4. Freeness of a matrix with free semicircular/circular entries from M_k(A_0).
5. Shlyakhtenko (arXiv math/9812079v1): Definition 2.3 (sup over conditioning models, limsup), Proposition 2.8, Theorem 2.19, Theorem 4.1 (proof omitted in the source; the hypotheses were checked literally), and the proof constant of Proposition 4.2.
6. Existence of conjugate systems implies well-definedness of difference quotients on the generated algebra (Voiculescu, Part V).

The Nica-Shlyakhtenko-Speicher results read (math/9809080 Proposition 4.1, math/9809081 Theorem 3.1) are NOT used by the final proof. The packet correctly records them as context only (normal-slice-construction.md line 59).

## REQUIRED blocking gaps

None.

## Optional (non-blocking) repairs

1. Stale status text. matched-volume-attempt.md line 1 ("under construction"), line 70 ("Remaining scrutiny point"), line 112 ("not yet sealed"); unconditional-score-construction.md §5 ("What remains unpaid"); and normal-slice-construction.md lines 44-61 ("Strict gap transfer remains unproved") predate the closing arguments in F, G and candidate.md. A manuscript should mark them as superseded.
2. State the rank lemma behind C.3/C.4 explicitly: rank-m change ⇒ trace-word change ≤ 2L R^L m/N.
3. State the uniform-in-microstate form of Lemma C with its compactness proof (§4 above).
4. Replace "triangular shear of determinant one" (matched-volume-attempt.md line 23) by the local-coordinate Jacobian computation in §2 above.
5. In the Theorem 4.1 application, name B = alg(T), give the B[t] representation by grouping T-letters, and state self-adjointness of both F and G (§8 above).
6. Derive χ(H) ≥ χ(H|B) from Proposition 2.8 plus the obvious inclusion rather than citing Proposition 2.12's reader-left equality.
7. Cite Proposition 4.2 through its proof constant n/2 and note the printed typo.
8. In C.4, note that the number of truncated Hermitian parts (2k² per coordinate) is a fixed constant multiplying the o(N) rank loss. The finite simulation showed rank loss of 3-6 times the inserted bad dimensions, consistent with this.
9. No quantitative ε or low-dimensional witness exists for k = 2^32. This is not needed for the existential target, and the packet already says so.

## Finite diagnostics (support only)

All are reviewer-written and independent of the author and round-1 code. They test finite identities and finite geometry only. They do not test conjugate-variable existence, entropy limits or primary theorems.

- `checks/exact_adjoint.py` → `exact_adjoint.json`: exact rational identities (§6), with 2 negative controls detected for k = 2, 3.
- `checks/finite_geometry.py` → `finite_geometry.json`: coarse inverse (§1), noise covariance (§7), almost-commutation (§2), the arbitrary-size recovery pipeline (§4), and unitary/quotient volume asymptotics (§2). In recovery runs with inserted junk, recovered-moment errors of order 0.003-0.12 at d = 94-160 reflect the deliberately inserted large finite-rank perturbations at finite size. They are exact (≈1e-12) without junk. Development bugs fixed during writing (SVD shape, coefficient extraction, an initially crude truncation threshold) are recorded in checks/README.md.

## Integrity

- The author verifier ran read-only: `python3 -I verify.py --anchor b6c5…beb3 --repo <repo>` → PASS (20 payload files, 19 canonical blobs, 3 primary pdf/text pairs). Recomputed SHAs are recorded in `checks/author-verifier-run.json`.
- `checks/verifier_controls.py` ran the author verifier on a temporary copy under /var/tmp (deleted afterwards), with 8 controls: positive, wrong anchor, altered candidate, missing candidate, extra public file, altered tree, altered source body, altered primary pdf. All behaved as expected (`checks/author-verifier-controls.json`). One expected-reason string was first mis-specified by the reviewer and then corrected; the verifier was never at fault.
- This review packet is sealed by `MANIFEST.json`, whose SHA256 is reported outside the packet. `python3 -I -B verify.py --anchor <sha>` checks it read-only (exact file membership, regular single-link files, sizes, SHA256). `verify_controls.py` → `checks/own-verifier-controls.json` runs 1 positive and 8 negative controls on a temporary copy: wrong anchor, appended file, same-size byte flip, missing file, extra file, edited manifest, symlink, hardlink. All behaved as expected.
