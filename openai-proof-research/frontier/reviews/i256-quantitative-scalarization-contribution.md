# I256 — contribution gate for complete quantitative scalarization

**Verdict: TECHNICAL.** Q1–Q4 is a useful explicit quantitative extension of R016, with meaningful uniformity. The inspected primary literature does not already contain its full specified-witness Schmidt recovery theorem. Its incremental argument beyond the accepted rank mechanism, however, consists of explicit energy bounds, weighted averaging, minmax perturbation and generic singular-pair stationarity. It does not clear the requested nonroutine-advance threshold as a separate substantial finding.

This is solely a contribution verdict, conditional on the separate proof gate accepting the exact candidate. It is not a proof rejection, a KNOWN verdict, or authorization to change the supplied ten accepted findings toward twenty.

The complete reviewed artifact is [I247 analytic-attempt.md](../experiments/i247_quantitative_complete_rigidity/analytic-attempt.md), SHA256 `7d8b629513741abab53339c19bb05c9f611ecbd0af1b6ace3246dff8af0eae8b`, independently matched to its actual bytes. The original discovery brief, complete final report and source-context records were read. This fresh I256 round used no interrupted I252 files, later/live review outputs, author rebuttal or repairs.

## Exact scope

Let d≥2, K=W(A)⊂R Dbar have interior, dist(σ(A),∂K)≥δ>0, and let ∂K contain a regular analytic arc of length at least ℓ on which the maximal support eigenvalue is simple with gap at least g. Set

    C0=8(d−1)R(3R)^(d−1)δ^(−d)[9πR²/(gℓ)+1/√6].

For every finite coefficient size m, every finite-degree matrix polynomial P normalized by max_K||P||=1, every 0≤ε≤1/2 with γ=||P[A]||≥2−ε, and every unit maximal singular pair x=vec X,y=vec Y, the candidate bounds both squared Schmidt tails by min(1,C0√ε). Leading product-vector errors are bounded by √(2C0)ε^(1/4). Their coefficient factors u,v give p=v*P u with max_K|p|≤1 and

    ||p(A)||≥γ[1−t_X−t_Y−√(t_Xt_Y)]≥2−ε−6C0√ε.

The active reducing-block extension yields scalar existence with the correct normalization on full W(A). It does not give every-pair control for maximal pairs mixing arbitrary active blocks of the full direct sum. No disk proximity, optimal exponent/constant, whole-P approximation or amplified output nilpotent rigidity is included in this assessment.

## Why the quantitative increment remains technical

R016/I242 already connects complete residual slack to the rank of the **original** positive boundary field. I242's Lemma S is conditional in arbitrary dimension, uses an arbitrary maximal singular pair, and forces both ranks one on a simple-support arc. I242 Section 7 also identifies positive-slack control on a fixed nondegenerate arc and the missing uniform control across collapsing geometric strata. I247 supplies explicit lower bounds for the support gap, arc length and spectrum-to-boundary distance, rather than resolving those degenerations.

The new arclength weighting is useful: with b=||H^(1/2)DH^(1/2)||HS and ∫b²≤S, the identity ∫_I|q|≥ℓ/(2π) gives ∫_I|q|²≥ℓ²/(4π²), hence inf_I b/|q|≤2π√S/ℓ. It genuinely avoids imposing a lower conformal-speed or harmonic-measure bound. It is weighted Cauchy–Schwarz/averaging applied to the same rank-(d−1) arc, with no new geometric propagation or degeneration control.

The small-overlap correction is also explicit and useful. Interlacing gives λ2(D)≤η. On the leading two-dimensional spectral space of XX*, with a2=λ2(XX*) and κ=||X*Y||, minmax gives a2−κ²/a2≤η, so a2≤η+κ. Exchanging X,Y yields the two tails. This is a direct perturbation of the old orthogonal-inertia mechanism at the square-root scale set by the inherited squared residual.

Finally, if x0=ax+e and y0=by+f with e⊥x,f⊥y, the two singular equations give y0*T x0=γab+f*T e for any operator T. The cancellation improves scalar loss from the naive fourth root to the square root, without a top singular-value gap. It is the generic stationary identity for a maximal singular pair; once tails are known, it is a routine variational improvement.

The joint payoff is an explicit recovery theorem, not empty bookkeeping. Nevertheless the structural bridge, arbitrary-pair scope, scalar compression and uniform energy structure are already established before I247. The present hypotheses provide their quantitative coercivity, and these elementary estimates complete the perturbation. On the user's stated standard, this is technical progress beyond R016 rather than a second substantial structural discovery.

## Primary overlap and uniformity

I read actual primary statements and full relevant proofs, not only abstracts:

- **Pinned direct and structural companions:** their relevant retained statements and proofs matched independently fetched raw bytes and pinned tree blobs. They supply the all-degree, all-coefficient complete residual and common representation, not Q2–Q4. Their original mass-two field and similar-matrix mass-one density were kept distinct.
- **ACV v3, Sections 3, 5, 7, 9, 10 and 11:** rectangular compression and exact Schmidt orthogonality leave the dimension-four (2,2) configuration; scalar/tuple iterate stability and scalar-value nilpotent approximation do not recover tensor factors of arbitrary P[A]. Scalar representing-measure and inverse-algebra results do not fill this gap. [ACV v3](https://arxiv.org/html/2608.27346v3).
- **Jin v2:** Sections 1–8 and Corollary 1 fully read; Section 9's stability statements and full Lemma 11/Proposition 7/Theorem 3 arguments read. These supply scalar exact disk rigidity and a compactness modulus, not complete coefficient recovery or a power-law disk conclusion. [Jin v2](https://www.preprints.org/manuscript/202609.0079/v2).
- **Poisson-kernel primary v3, Propositions 7–8:** full relevant proofs read. Proposition 8's proof already gives the positive-spectrum lower bound γ_H/||σ0I−A||². I247's local Q8 bound is its multiplicity-one form after multiplication by 2|q|. This ingredient is prior art; the paper does not state the complete recovery theorem. [Primary v3](https://www.preprints.org/manuscript/202602.0563/v3).

For fixed d,R,δ,g,ℓ, the recovery tends to zero even when m, degree and coefficient magnitudes grow. That uniformity is real, stronger than compactness at fixed witness size, and not rejected because the constant is large. Its source is the inherited residual's dependence on unit-HS tensor factors and the base resolvent, with no polynomial coefficient sum. Preserving it through the added estimates does not by itself meet the nonroutine criterion.

Bounded current searches found no primary statement matching the full theorem. Thus **KNOWN** is not supported. Nor is worldwide priority certified. Lack of exhaustive priority alone is not the reason for this verdict.

## Limits and disposition

The stadium family shows why every-pair recovery can fail when the support gap collapses; it does not prove optimal gap dependence or solve scalar existence through that degeneration. The weighted-chain and unused-channel examples correctly block output rigidity and whole-P approximation. These boundaries should remain attached to the technical result.

Disk geometry is expressly excluded. Its omission is not an automatic failure of the narrower scalarization gate; the TECHNICAL classification concerns that increment itself. The original broader quantitative rigidity program remains unresolved.

No local proof repair is requested by this contribution review. Improved constants, a renamed statement or a compactness modulus would not answer the objection. A further independently proved structural result addressing an actual remaining barrier could warrant reassessment; none has been supplied here. Preserve Q1–Q4 as technical progress subject to its separate proof gate, and leave acceptance/count decisions to the parent.

Full reasoning: [analysis.md](../experiments/i256_quantitative_scalarization_contribution/analysis.md). Exact source scopes and searches: [literature.md](../sources/i256_quantitative_scalarization_contribution/literature.md). Read/access record: [reading-and-failures.md](../experiments/i256_quantitative_scalarization_contribution/reading-and-failures.md). Detached-byte provenance: [input-authentication.json](../experiments/i256_quantitative_scalarization_contribution/input-authentication.json). Its own digest is returned separately to avoid self-reference.
