# R012 — Dimension- and label-uniform Gaussian propeller stability

**Accepted as the sixth substantial finding.** Under the stipulated truth of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, the [complete I38 proof](../iterations/i38-inequality-stability-discovery.md) passes [independent full-proof review without repairs](../reviews/i38-propeller-stability-r2.md). The [separate significance review](../reviews/i38-propeller-stability-novelty-r3.md) recommends SUBSTANTIAL for the full uniform theorem. Parent reproduction passes. This is one finding; worldwide priority, human peer review and formal proof certification are not established.

## Exact theorem

Let \(d\ge2\) and \(k\ge3\) be arbitrary finite integers, and let \(A=(A_1,\ldots,A_k)\) be a measurable partition of standard Gaussian space \((\mathbb R^d,\gamma_d)\), modulo null sets. Empty cells are allowed. Define
\[
 B=\frac{3}{2\sqrt{2\pi}},\qquad
 z_i=\int_{A_i}x\,d\gamma_d(x),\qquad
 \Delta(A)=B^2-\sum_{i=1}^k\|z_i\|^2.
\]
Let \(\mathcal P_{d,k}\) consist of partitions into three origin-centered \(120^\circ\) sectors in a two-dimensional linear subspace, extended by its orthogonal complement, and \(k-3\) empty cells. Include every orthogonal rotation and label permutation. Set
\[
 d_P(A)=\inf_{P\in\mathcal P_{d,k}}
          \frac12\sum_{i=1}^k\gamma_d(A_i\triangle P_i).
\]
This is the least probability of a label disagreement after alignment.

There exists a single numerical constant \(c_P>0\), independent of \(d,k\) and every cell mass, such that
\[
 \boxed{\quad \Delta(A)\ge c_P\,d_P(A)^2.\quad}
\]
No prescribed masses, positive-mass lower bounds, regular boundaries, connectedness, or translation quotient are imposed. The theorem is uniform over all finite dimensions and finite label counts; it does not assert a partition-distance theorem for infinitely many labels.

It follows that, after selecting three labels, the total mass outside them and each selected mass's deviation from \(1/3\) are at most \(c_P^{-1/2}\sqrt{\Delta}\). These are consequences of the same result, not additional findings.

The exponent \(1/2\) in the distance bound is sharp. For planar consecutive sectors with openings \(2\pi/3+t,2\pi/3-t,2\pi/3\),
\[
 \Delta=\frac{1-\cos t}{4\pi},\qquad
 d_P=\frac{t}{2\pi},\qquad
 \frac{\Delta}{d_P^2}\longrightarrow\frac{\pi}{2}.
\]
This does not claim an optimal numerical value of \(c_P\).

## Constant and proof dependencies

The constant is positive but implicit. For any finite norm-one Gaussian score array \(v=(v_i)\), order its norms decreasingly, pad with zeros, and put
\[
 M(v)=\mathbb E\max(0,\langle v_1,g\rangle,\ldots),\qquad e(v)=B-M(v).
\]
For its first three vectors set \(\mu=(v_1+v_2+v_3)/3\), \(u_i=v_i-\mu\),
\[
 E=\sum_{i>3}\|v_i\|^2+3\|\mu\|^2,
\]
and let \(\alpha\ge\beta\ge0\) be the two singular values of the centered three-column matrix. Define
\[
 E_0=(B/1600)^2,\quad
 \eta=\inf_{\substack{\text{all finite norm-one arrays}\\
 E\ge E_0\ \text{or}\ \beta\le1/(2\sqrt2)}}e(v).
\]
The proof establishes \(\eta>0\), uniformly over array lengths and dimensions. With
\[
 c_0=\frac{3}{128\sqrt{2\pi}},\qquad
 c_V=\min(c_0,\eta/4),\qquad
 c_P=\left[36\left(B^{-1}+(2c_V)^{-1}\right)\right]^{-1},
\]
the stated theorem holds. No numerical search is claimed to compute \(\eta\).

The main pinned input is *The Gaussian propeller bound in every dimension*, September 24, 2026: its sharp inequality and finite Gaussian-score duality, extremizer structure, scalar estimates, residual determinant bounds, and elimination certificates. [Exact source contracts](../sources/i38_inequality_stability_discovery/source-contracts.json) identify files, labels and immutable URLs. The equality endpoint also uses Heilman–Jagannath–Naor's dimension-three uniqueness interface, explicitly present in the retained Princeton author PDF, Remark 1.4. R2 checks the distinction from arXiv v2 and the strict exclusion supporting that interface. Its original large computer proof was not rerun.

The full proof remains in the unchanged I38 report; its independently checked argument is:

1. Extend the finite score inequality to countable square-summable vectors in an isonormal Gaussian process. At equality, first-chaos moments satisfy \(z_i=Bv_i\), sum strongly to zero, and have nonpositive pairwise inner products.
2. Exclude infinite-support equality lists using three fixed positive-radius competitors against a radius \(t\to0\). The source residual calculation gives \(\tfrac32(c-t^2)^2\le10(3/\pi)^2t^2\), impossible for fixed \(c>0\). The endpoint-compatible finite elimination and HJN uniqueness classify all equality lists as an equilateral triple and zeros.
3. Compactify sorted Gram matrices. The bound \(\|v_i\|^2\le1/i\) gives uniformly vanishing expected Gaussian tail maxima. Sharpness forces the limiting Gram trace to equal one, preventing energy escape. Equality classification then establishes \(\eta>0\). Compactness supplies neighborhood entry, not a power law.
4. In that neighborhood, the centered three-score support dominates \(hR\), where \(h=1/(4\sqrt3)\) and \(R\) is planar Gaussian radius. The aggregate activation of arbitrarily correlated extra scores and the head's common mean is at most \(400E^{3/2}\). A Gaussian trace-moment bound and the independent planar radial integral supply the cubic power. It is subordinate to the normalization loss of order \(E\).
5. Exact triangle geometry and polar alignment give \(e(v)\ge c_V\operatorname{dist}(v,\mathcal T)^2\), where \(\mathcal T\) is the equilateral-triple array class. For \(F=\sum\|z_i\|^2>0\), use \(v=z/\sqrt F\). The squared pairing identity bounds aligned score regret by \((B^{-1}+(2c_V)^{-1})\Delta\). Three Gaussian boundary slabs, with one zero-score event covering every inactive label, give regret at least \(d_P^2/36\). The case \(F=0\) is immediate.

## Significance and novelty limits

Heilman's 2014 Lemma 2.8 already gives quantitative three-cell propeller stability, implying \(d_P\le18\Delta^{1/4}\). Later three-candidate angular and radial penalties are also genuine antecedents. The determinant inequality, equality classification, ordinary Gaussian tail tools, finite-three-cell exponent improvement and calibration are not separately claimed as new mechanisms.

The additional step is uniform control at the boundary where arbitrarily many labels disappear. Exact optimizer elimination does not apply to near optimizers: adding \(N\) orthogonal scores of total energy \(E\) to a rescaled equilateral triple produces near-optimal winning partitions with \(N+3\) active cells for arbitrarily large \(N\). The compactification and cubic aggregate activation estimate control their combined effect without a mass or label-count parameter.

The final review also supplies a simpler summation of individual third moments yielding the same cubic estimate. It corrects any suggestion that summing per-label estimates is inherently incapable of uniformity. This is a simplification, not a repair; the contribution is the aggregate activation-versus-normalization comparison, not one particular way of bounding its third moment.

The bounded primary comparison includes exact source and companion operations, Khot–Naor, HJN, Heilman's quantitative partition papers, Gaussian width and vector-max stability, quantitative duality, and quantization margin results. Generic duality transfers presuppose primal stability; fixed-mass, unit-variance or isotropic normalization results do not directly supply this boundary estimate. See the full R3 review for exact hypotheses, versions and reductions.

Acceptance means that the complete deduction and its additional mechanism meet this project's review standard relative to the sources examined. It does not establish worldwide first discovery, optimal constants, effective computation of the global gap, or independent truth of the stipulated corpus.

## Validation and provenance

- [Author parent verification](../experiments/i38-parent-verification.json): both author commands pass, with 93 author files unchanged.
- [R2 parent verification](../experiments/i38-r2-parent-verification.json): proof audit and combined reproduction pass; 161 author/reviewer files unchanged.
- [R3 parent verification](../experiments/i38-r3-parent-verification.json): 110 sealed R3 artifacts, fourteen frozen inputs, thirteen selected pinned files, 39 primary responses including one documented failure, 49 logged passages, and 859 exact finite checks pass. All 9,340 corpus files match the complete 749-manuscript inventory. Both prior verifiers reproduce with output writes intercepted; all 274 monitored files across the three rounds remain unchanged.

Numerical quadrature and pointwise stress tests retain their non-certified status. They are diagnostics, not universal analytic proofs. No HJN computer certificate was relabelled as a new computation. Shared-ledger changes after integration are expected mutable drift; sealed proof and source bytes remain unchanged.

Candidate integration: local commit `4d6c9f00`; proof integration: `a1d77060`. This record and the R3 integration receive a separate acceptance commit. [Publication instructions and mapping](../../PUBLICATION.md) explain the project-only filtered public history.

