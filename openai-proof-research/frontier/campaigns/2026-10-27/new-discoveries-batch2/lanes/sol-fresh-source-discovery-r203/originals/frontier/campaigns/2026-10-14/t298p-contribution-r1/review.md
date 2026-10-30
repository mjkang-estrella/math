# T298P independent contribution review r1

Role: contribution and eligibility only, **conditional on correctness**. Correctness belongs to the separate proof gate. I did not read, request or infer its outputs, and no `t298p-proof*` path was opened. The pinned OpenAI theorems and their proof operations at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated. External primary results are applied only under their stated hypotheses. This verdict changes no count and accepts nothing; only the parent can accept.

Reviewed object: author manifest `b6c525288bd6a7203d13c8b8ed4b696e14a0f8c3a06cd30cb6fbe871d6dfbeb3`. All seven dispatched anchors and the 13223-entry tree anchor `eeecc1da…5e09b` were matched by sha256sum. Frozen scope: `scope-freeze.md` `8e9b3f5f…589e`.

Full target, unchanged: there exist exactly two bounded self-adjoint elements Z1,Z2 in a von Neumann algebra with faithful normal tracial state such that −∞ < χ(Z1,Z2) < χ*(Z1,Z2) < ∞. Here χ is the original operator-norm-cutoff, limsup-over-matrix-sizes microstates entropy, with unnormalized Hilbert–Schmidt Lebesgue volume.

## Verdict

**SUBSTANTIAL**, conditional on correctness, for the full unchanged two-variable target.

- **Not DUPLICATE.** The read primaries, the pinned source and companions, the bounded literature search and the campaign history contain no two-variable finite strict χ/χ* gap. None contains an unconditional matrix-amplification identity for χ and χ* that would yield one. Source298's own introduction says its construction "does not address equality for every smaller prescribed number of variables" (01-introduction.tex, after Theorem `thm:main`). The only prior campaign record on family 298 (analytic r20, `entropy-obstruction.md`) screened noise persistence, not variable reduction.
- **Not INELIGIBLE.** The candidate claims the full frozen target, plus a stronger liminf transfer (1). Neither is relative, ultrafilter-only, many-variable, −∞-entropy, factor-isomorphism, or conditional on matrix units. Entropy depends only on the joint law, so the pair need not generate its ambient algebra.
- **Not BLOCKED.** I read every closest operation that could pay the bridge: the full Shlyakhtenko and NSS R-diagonal texts, NSS Fisher Prop. 4.1 with its proof, and the full source298. Contribution is assessable conditional on correctness.
- **Not TECHNICAL.** I tried each available reduction of the bridge to paid operations (§2). Each fails at an identified operation, and two fail quantitatively, through divergent gauge-orbit terms. Two unconditional estimates carry the transfer, and no read source supplies either one:
  - U1, an orbit-direction-cheap Fisher bound;
  - U2, an all-size matched normal-tube volume upper bound.
  
  Their coupling U3 makes the gauge orbit entropy-neutral to O(ε) in both theories at once. I am not inferring novelty from the absent two-variable statement, from the proof's length, or from audit effort.

### Conditions of this verdict (not objections to frozen bytes)

The classification assumes the separate proof gate passes the unchanged argument, specifically:

- **(a)** inequality (3), unconditional. No relative-to-M_k score is discarded into an unconditional bound, and no upper Fisher continuity is used.
- **(b)** the upper half of (2) for every output size N, at the ordinary limsup, with the same C_D as the lower half.
- **(c)** the noisy-endpoint lower bound via Shlyakhtenko Thms. 2.19 and 4.1 under their printed hypotheses.

If (a) or (b) is repaired by a different mechanism, this classification must be redone. If either is replaced by a relative, ultrafilter, or multiples-of-k-only statement, the frozen target is not met.

## 1. Operation ledger

| Candidate step | Closest paid operation (actually read) | Added by T298P |
|---|---|---|
| Base pair D with scalar commutant; tangent rank k²−1; normal dimension k²+1; 2k² = (k²−1)+(k²+1) | Finite linear algebra. Reproduced exactly for path trees, k=2..6 (C1) | Choice of encoding: routine on its own |
| Finite χ of E_ε(X) (finite-entropy-chart.md) | Local chart, Jacobian, source298 GUE norm tail (`eq:gue-norm-tail`), source subsequence selection (Lemma `lem:flow` style) | Technical |
| Orbit × slice measure factorization; orbit constant c = 3/4 + ½log2π | NSS math/9809081v1 Lemma 2.6 (measure-preserving polar map, C_k = Vol U(k) for Re Tr(ab*)), Lemma 2.8 (the limit 3/4 + ½log2π, via Marinov), Lemma 2.9 (orbit upper bound), Lemma 2.10 (orbit lower bound via strengthened asymptotic freeness). C4 confirms the candidate's c is the same constant in the same unnormalized HS metric | Paid constant. C_D exponent bookkeeping is routine; C5 confirms exact cancellation of log d and log k |
| Lower half of (2): bundle over source microstates, source subsequences retained as kd | NSS Lemma 2.10 pattern; Shlyakhtenko §5 second claim (measure-preserving packing of entry microstates into matrix microstates) | Global tube injectivity: technical |
| **U2.** Upper half of (2) for arbitrary N: band projections of trace exactly 1/k, tree-polar truncation and common-root intersection, second root truncation, normal-tube inversion back to source microstates, projection η-nets and complement-volume cost θlog(C/θ)+θlog(C/η), ordinary limsup | NSS Lemma 2.9 is exact only because every matrix has a polar decomposition, so the orbit chart covers all of M_k. Shlyakhtenko §5 first claim compresses to a corner p ≤ e11 of **supplied conditioning** matrix-unit microstates (e_ij ∈ Γ(E_ij : …)); it is an equality only along ultrafilters, and its ordinary-limsup statement is one-sided (χ(entries) ≤ N²χ(Z\|B⊗M_N) − …) | **Unpaid.** Matrix units are recovered from the pair's own microstates, which need not be operator-norm near the orbit. The result is an unconditional upper bound with the same constant as the lower bound |
| **U1.** Unconditional Φ*(Z) ≤ Φ*(U)/(ε²k⁴) + Cε⁻¹(1+Φ*(U)) via coarse-bimodule normal derivations plus inner derivations, Neumann series and projection | NSS math/9809080v1 Prop. 4.1: Φ*({g_ij}:B) = d³Φ*(G:M_d(B)), relative to M_d(B), plus the projection Φ*(G) ≤ Φ*(G:M_d(ℂ)) | **Unpaid.** The paid route diverges for this encoding (§2(b)). Inner derivations replace the relative orbital cost (k²−1)/u by O(1) adjoint norms, so the orbit part is O(ε) after integration |
| Exact free normal/orbital noise decomposition at t = ε²k²u | Orthogonal invariance of free semicircular systems; the coefficient normalization "2k² semicirculars divided by k" (exact completeness identity, C2) | Routine identity. Its role, keeping the whole heat path inside the encoded form so U1 applies uniformly, is part of U3 |
| Noisy-endpoint straightening H_ε = U + εR_ε; χ(H) ≥ χ(H\|T) = χ(U) − O(ε) | Shlyakhtenko math/9812079v1 Prop. 2.8 with Voiculescu χ(X:Y) ≤ χ(X); Thm. 2.19 (for p=n the fiber bound λΓ(X\|y) ≥ (1−δ)λΓ(X) holds for every large size, so the ordinary limsup is preserved); Thm. 4.1 (change of variables; its proof is omitted in v1) | The contraction construction of the inverse NC series is technical |
| **U3.** Same C_D at both endpoints, with gap ≥ k⁻²[g − gap(X+√U₀S)] − O(ε) | — | **Unpaid coupling** of U1 and U2 |
| Large-noise source gap → 0; strictness; finiteness | Shlyakhtenko Prop. 4.2 (χ(X+√tS) ≥ (n/2)log2πet for embeddable W*(X); the printed "n log" is a typo for n/2 by its proof); Voiculescu covariance bound for χ*; χ ≤ χ* (Biane–Capitaine–Guionnet, Jekel–Pi); source298 heat-flow identity (`eq:freeflow`) | Routine |

## 2. Attempted reductions to paid operations (all fail)

**(a) Pure packing with free fillers, plus Shlyakhtenko §5 and NSS 4.1.** Put Y = (X, S′), where S′ is a free semicircular (k²−1)-tuple, and let Z be the k×k Hermitian pair with entries Y.

- The relative gap is k⁻²·gap(Y) = k⁻²·gap(X), but only along ultrafilters on the χ side.
- Removing the conditioning needs the excess χ(Z) − χ(Z\|M_k) to be no larger than χ*(Z) − χ*(Z:M_k) up to less than the relative gap.
- No read source controls this. NSS Thm. 3.1 uses χ(Z\|M_k) ≤ χ(Z) one-sidedly, and has equality only when Z is free from 1⊗M_d.

Fails.

**(b) The candidate's own encoding with only paid relative tools.** At u = 0 the 2k² real entries of E_ε(X) lie in a (k²+1)-dimensional affine family, so χ(entries) = −∞ and Φ*(entries) = ∞. At u > 0 the entries are an orthogonal-times-ε image of (U(u), T(u)), with T(u) = √u R orbital and Φ*(T(u)) = (k²−1)/u.

- *Fisher side.* NSS 4.1 with projection gives Φ*(Z_t) ≤ Φ*(Z_t:M_k) = [Φ*(U(u)) + (k²−1)/u]/(ε²k⁴). The scale 1/(ε²k⁴) is checked against the semicircular case in C2. With dt = ε²k²du, the χ* increment bound is (1/2k²)∫₀^{U₀}[Φ*(U(u)) + (k²−1)/u]du. Its orbital part is ((k²−1)/(2k²))·log(U₀/u₀) → +∞ as u₀ → 0 (C3). The trivial bound Φ* ≤ 2/t also fails to integrate at t = 0.
- *Microstates side.* Shlyakhtenko §5 gives χ(Z_t) ≥ χ(Z_t\|M_k) ≥ k⁻²[χ(U(u)) + ((k²−1)/2)·log(2πeu)] + const, and this tends to −∞ as u → 0.

Both paid routes therefore lose the gauge orbit at the starting point, where T298P needs O(ε) control. Fails, quantitatively.

**(c) Conditioning on matrix units inside W*(Z).** Take the band and tree-polar matrix units f_ij ∈ W*(E_ε(X)) and condition on them. The f_ii are spectral projections of Z1, so the off-diagonal f-entries of Z1 vanish identically.

- *Fisher side.* NSS Prop. 4.1, applied in M ≅ M_k(f11 M f11), gives Φ*(Z:{f_ij}) = k⁻³·Φ*(entries) = ∞, because a zero variable has no conjugate variable. Projection then yields no bound on Φ*(Z).
- *Microstates side.* χ(entries) = −∞ is on the small side of Shlyakhtenko's one-sided §5 inequality, which therefore says nothing. The unconditional excess is exactly the gauge-orbit term that U2 computes. No read source supplies this "gauge-fixing" identity unconditionally.

Fails.

**(d) Free Haar rotation.** uZu* with u Haar and free has the law of Z and is free from M_k, so χ(Z) = χ(uZu*\|M_k). However, the entries of uZu* are not the source tuple. This is a tautology and transfers nothing. Fails.

**(e) Generator or isomorphism routes.**

- Companion287 (`entropy-dimensions.tex`, Cor. `cor:entropy-dimensions`; `amplification.tex`) transports tuples coordinatewise. It preserves length and joint law and explicitly shows that the dimensions change under W*-generator replacement.
- The pinned preprint *Relative generation and the generator problem for finite factors* (Sept 23 2026; introduction Theorem `thm:main`: every separable II₁ factor is generated by two self-adjoints; Cor. `cor:entropy-generators`) supplies W*-generation by two elements. Its own corollary records that δ and δ₀ change under replacement of generators: a pair has dimension ≤ 2 < n.

Generation by two elements therefore says nothing about the entropies of the generating pair. Factor isomorphism is not entropy invariance. Fails.

**(f) The source block witness with one or two signals.** encoding-attempt.md §3 shows the copied terminal event becomes typical. Partitioning by eigenspaces of D1 gives compressed energy ≥ ‖D1‖² → v > r/16. I checked this at contribution level; it is a sound obstruction to that copied witness only. Fails for the source mechanism.

**(g) Dimension-level amplification.** Two results were seen by abstract or snippet only:

- Jung math/0410594 Lemma 3.1: δ₀(x⊗I_p, matrix units) = 1 − 1/p² + δ₀(x)/p², with the matrix units included among the generators.
- Shlyakhtenko arXiv:2201.09503: an approximate Schreier-type δ* inequality.

Both are first-order (dimension) statements and do not pay finite-part χ or χ* values. Fails.

Robustness: if an unread orbital-free-entropy result (Hiai–Miyamoto–Ueda; Ueda) paid part of U2, U1 would remain unpaid, because orbital free entropy is a microstates notion. The classification would not change. It would change only if an unconditional nonmicrostates gauge-orbit Fisher estimate were found as well.

## 3. Why this is a contribution, stated at operation level

The source theorem is used purely as a black box: its finite-gap tuple, finite Fisher information, embeddability and boundedness. The new engine is a **gap-preserving unconditional reduction from k²+1 variables to 2**, with gap factor k⁻². It works because:

- the base pair has scalar commutant, so the gauge orbit has full dimension k²−1;
- on the microstates side, the orbit contributes the same volume constant C_D at both noise endpoints. This needs the unconditional all-size upper recovery bound U2.
- on the nonmicrostates side, inner derivations make orbit directions cost O(1) score norm instead of the relative (k²−1)/u. This is U1.
- the exact free normal/orbital decomposition keeps the heat path inside the encoding.

Each ingredient is classical, as the author acknowledges. The combination proves two unconditional estimates that the paid relative theory provably cannot deliver for this encoding (§2(b)), and that classical work had left as the one-sided inequalities χ(Z\|M_k) ≤ χ(Z) and Φ*(Z) ≤ Φ*(Z:M_k). The result answers the variable-count limitation stated in the source at the minimal nontrivial case, since one-variable χ = χ* is classical.

## 4. REQUIRED objections (attribution/comparison; none alters frozen bytes or the verdict)

1. **Narrow and credit the orbit-volume component.** comparison.md lists "a global associated normal bundle gives matching chi volume constants" inside the claimed new operation. Several parts are paid and must be credited:
   - the orbit × slice factorization pattern and the constant c = 3/4 + ½log2π: NSS math/9809081v1 Lemmas 2.6, 2.8, 2.9, 2.10, with Lemma 2.8's limit in the same Re Tr metric (reproduced in C4);
   - the unitary-volume formula.
   
   The claimed microstates novelty must be stated as U2 (unconditional, all N, intrinsic matrix-unit recovery, rank-loss accounting, ordinary limsup) together with the coupling U3. Global tube injectivity is technical support.
2. **Credit Shlyakhtenko §5's corner/compression pattern.** That pattern is a projection p ≤ e11 with [e11,p] = 0, compression maps T, and measure-preserving packing. State that §5 conditions on supplied matrix-unit microstates and is an equality only along ultrafilters. Its one-sided ordinary-limsup inequality is not used.
3. **Cite the paid results now referenced generically.** These are:
   - Shlyakhtenko Prop. 4.2, for the Gaussian lower bound in candidate §5 and matched-volume E (hypothesis: W*(X) embeddable; note the printed constant typo);
   - Voiculescu's covariance bound, for χ*;
   - Biane–Capitaine–Guionnet and Jekel–Pi, for χ ≤ χ*;
   - Shlyakhtenko Prop. 2.8 with χ(X:Y) ≤ χ(X), for χ(H) ≥ χ(H\|T);
   - source298 (`eq:chistar`, `eq:freeflow`), for the heat-flow identity.
4. **Address the pinned generator-problem preprint.** *Relative generation and the generator problem for finite factors* (Theorem `thm:main`, Cor. `cor:entropy-generators`) is the same-corpus two-generator result. The packet's comparison omits it. Any acceptance record or manuscript must state that it pays W*-generation only and that its own corollary shows the entropy invariants are generator-dependent. Otherwise "source298 plus the pinned two-generator theorem" appears to give the target, and it does not.

## 5. Optional

1. Add the quantitative failure of the paid route (§2(b), C3) to the comparison. It is the cleanest operation-level reason the result is not a transfer.
2. If the argument is general, state the transfer theorem for every bounded, embeddable (k²+1)-tuple with finite χ and Φ* < ∞ (k ≥ 2), then specialize to source298. This is presentation only; the frozen scope is unchanged.
3. Present the free normal/orbital rotation and the 1/k coefficient normalization as classical, so the contribution is not located there.
4. Shlyakhtenko Thm. 4.1's proof is omitted in arXiv v1 ("almost identical to … [4]"). Cite a published version containing the argument, or flag the dependency explicitly. Whether its hypotheses (common multiradii, inverse identities, ‖X_i‖ < min(r_i,R_i), coefficients in B) are met is the proof gate's question.
5. In a manuscript, screen and cite the dimension-level and orbital analogues: Jung math/0410594; Shlyakhtenko 2201.09503; Hiai–Miyamoto–Ueda math/0702745; Ueda 1210.6421 and 1610.04118; Connes–Shlyakhtenko on inner derivations in δ*. I saw these at abstract or snippet level only.
6. The gap bound g/k² ≈ 2⁻⁶⁵ is existential. Say so explicitly, as candidate §Boundaries already does, so it is not read as a quantitative claim.

## 6. Evidence and limits

- `contribution-checks.py` and its output `contribution-checks.json` cover C1–C5. These are finite attribution and normalization checks; they prove no entropy or Fisher statement.
- `checks.json` records:
  - the author verifier (read before execution), which passed;
  - six copied author-verifier controls, each with its reason checked;
  - the anchor recomputation;
  - the provenance of the fetched pinned generator-preprint blobs.
- `reading-limits.md` gives the exact reading extent.
- No worldwide priority claim is made; the literature screen was bounded.
