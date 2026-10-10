# R013 — Higher-dimensional logarithmic Brunn–Minkowski stability

**Accepted as the seventh substantial finding.** Under the stipulated truth of `openai/math@fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, the [complete I49 proof](../iterations/i49-hard-moment-quantitative-stability.md) passes [I50’s independent full-proof audit without repairs](../reviews/i50-hard-moment-quantitative-stability-r2.md), including its original dimension-only exponent. [I51’s separate significance review](../reviews/i51-hard-moment-quantitative-stability-novelty.md) judges the integrated construction SUBSTANTIAL conditional on that proof approval; I50 now satisfies that condition. Parent reproduction passes with the verification qualifications below. This is one finding, not a claim of worldwide priority, human peer review or formal proof certification.

## Exact theorem

For every integer \(n\ge3\), there is a finite exponent \(\alpha_n\), depending only on \(n\), with the following property. Fix \(0<r<R\) and \(0<\tau_0<1/2\). There is \(c(n,r,R,\tau_0)>0\) such that every pair of full-dimensional origin-symmetric convex bodies satisfying
\[
rB\subset K,L\subset RB
\]
and every \(\lambda\in[\tau_0,1-\tau_0]\) obey
\[
\boxed{\quad
\log|\mathcal W[h_K^{1-\lambda}h_L^\lambda]|
 -(1-\lambda)\log|K|-\lambda\log|L|
 \ge c(n,r,R,\tau_0)\,d_{\mathcal E}(K,L)^{\alpha_n}.
\quad}
\]
Here \(B\) is the Euclidean unit ball, \(h_K\) is the support function, and
\[
\mathcal W[f]=\{x\in\mathbb R^n:x\cdot u\le f(u)\text{ for every }u\in S^{n-1}\}.
\]
The comparison class \(\mathcal E\) consists of all pairs
\[
K'=\sum_{i=1}^m D_i,\qquad L'=\sum_{i=1}^m c_iD_i,
\qquad \mathbb R^n=E_1\oplus\cdots\oplus E_m,\quad c_i>0,
\]
where the subspaces are nonzero and each \(D_i\subset E_i\) is an origin-symmetric convex body with nonempty relative interior. One block and nonorthogonal complementary subspaces are allowed. Define
\[
d_{\mathcal E}(K,L)=\inf_{(K',L')\in\mathcal E}
 \max\{d_H(K,K'),d_H(L,L')\}.
\]
Comparison bodies need not satisfy the original ball bounds. No regularity, common reflection, facet-count, minimum facet-mass or block-angle hypothesis is imposed on the input.

One deliberately weak permissible exponent is
\[
\alpha_n=\frac{64n(n+2)(a_n+b_n+1)}{b_n},
\]
where the explicit positive dimensional constants \(a_n,b_n\) are defined in I49 (5.2a) and checked, without enlargement of the displayed exponent, in I50 §4.2. They arise from John normalization, the hard moment Hessian cap, and dimensional core/tail bounds. The multiplicative theorem constant may depend on \(r,R,\tau_0\). No sharp or practically useful exponent is claimed.

## Proof and dependencies

The full proof remains in the unchanged I49 report. The accepted pinned inputs are the logarithmic Brunn–Minkowski manuscript’s finite-slab concavity, moment coordinates, adjunctions, dense even range, and tensor/variance operations. The exact selected files and immutable blob identities are recorded in the [source manifest](../sources/i49_hard_moment_quantitative_stability/selected-manifest.json).

Full attribution is retained for Liu–Sun–Xiong’s unnormalized tensor completion, regularizer, compactness and contact-measure mechanism in *The centered logarithmic Brunn–Minkowski inequality*, arXiv:2610.10152v2. The external centered nonsymmetric theorem is not assumed or established here. Berman–Berndtsson, Bonnet–Rubinstein, Cule–Samworth and Figalli–Jhaveri–Mooney supply the checked moment existence and local convergence interfaces; Klartag supplies the bounded hard-target Hessian cap. Hug–Schneider’s surface-area continuity and Figalli–Maggi–Pratelli’s anisotropic stability supply later geometric estimates. Their actual hypotheses and applications are audited in I50.

The independently checked chain is:

1. Fix the regularizer at a positive deficit budget and exhaust directions and slab powers. Select interior times with unnormalized curvature defect of that order. Complete dense tests before taking limits. Retain both the tensor derivative energy and the square controlling the derivative of the companion field.
2. Pass to hard moment coordinates at fixed regularizer. Local coefficient convergence and Sobolev compactness produce compatible fields with finite error, rather than only an equality limit. Positive joint contact measures pass the signed boundary identity. Keep its nonzero mean score, which records the endpoint volume slope.
3. Normalize the intermediate body by its John ellipsoid and a constant mean-Hessian frame. The hard Hessian cap and determinant/coercivity estimates give dimension-only exponential core and tail rates. Poincaré, symmetrization and spectral grouping yield approximate block structure at a logarithmic source radius.
4. Convert the position-test boundary residual to an absolute normal residual. The convex gauge’s Hessian measure bounds the radial normal map in BV. Smoothing the particular bounded Lipschitz residual gives an admissible position test, with a controlled power loss despite facets and ridges.
5. Average the moment gradient over complementary coordinates of a full cube. The mixed-Hessian estimate gives a uniform approximation after a Lipschitz upgrade. The product of the component image convex hulls is one compatible product body. Source-tail and cap estimates extend the comparison from the core image to the whole intermediate body.
6. Use surface-area continuity and the absolute residual to compare endpoint supports with two block dilations of that same product. Transfer only bounded Lipschitz absolute support differences between surface measures. Exact block Jacobians give the correctly oriented mixed-volume errors, while the retained mean/trace relation gives both endpoint volumes.
7. Apply anisotropic perimeter stability to each endpoint. Symmetric convex overlap removes translation; volume control removes dilation; cap estimates convert symmetric difference to Hausdorff distance. Balance the dimensional core/tail errors to obtain the stated power. An upper-budget limit covers zero deficit, and a fixed comparison pair covers larger deficits.

The direct Neumann construction and interval form-domain obstruction in I49 §4 are separately validated method diagnostics. They do not refute the theorem and are not additional findings.

## Significance and limits

The contribution is the combined finite-defect construction from the moment fields through a global product to both original endpoints. Individual compactness, BV smoothing, spectral grouping and classical stability tools are not separately claimed as new.

The significance review compares actual source operations with the strongest checked antecedents. LSX’s equality proof can use vanishing errors and exact contact identifications; these are unavailable at positive defect. Böröczky–De’s power theorem uses common reflections to obtain a coordinate inclusion. Böröczky–Henk’s product stability starts with almost saturated cone mass on an exact subspace, rather than merely nearby normals. Uniform scalar Brascamp–Lieb and moment-energy stability of Machado–Ramos requires its own finite scalar deficit or variational gap. None of these checked interfaces alone supplies the compatible product and two-endpoint data required here. I51’s verdict concerns that integrated step, not merely an exponent absent from a search result.

This does not certify worldwide first discovery or preclude a shorter proof. The bounded primary-source comparison, versions and attribution are retained in I51. The result is conditional on the user’s stipulated corpus, not an independent validation of it. It does not establish centered nonsymmetric stability. The earlier planar theorem retains its technical-only disposition; its consequences are not added to the count.

## Validation and provenance

- [I49 parent record](../experiments/i49-parent-verification.json): 163 sealed artifacts, 35 frozen inputs, 506 exact assertions and all 9,340 corpus files. The initial unmodified verifier failed at an order-sensitive raw search-output comparison. A later unmodified retry and a separate explicitly order-normalized in-memory replay passed. The original failure and unchanged author verifier remain preserved.
- [I50 parent record](../experiments/i50-parent-verification.json): 188 sealed artifacts, 110 frozen inputs, 35 passage records, thirteen successful fresh responses, nine PDF text replays and 310 independent exact assertions. Seven prior seals and 2,416 prior artifact checks pass. The analytic PASS is the written review’s conclusion, not inferred from finite diagnostics.
- [I51 parent record](../experiments/i51-parent-verification.json): 195 sealed artifacts, 55 frozen inputs, 61 passage records, 31 successful primary responses, nineteen PDF text replays and 309 independent exact assertions. Its normalized I49 replay is labeled separately. All corpus identities and prior seals pass.

The four shared ledgers have expected mutable drift after integration. No proof, source or historical seal was rewritten to make checks pass. Exact finite calculations test signs, tensor covariance, mixed-volume orientation and compatibility; they do not mechanically certify the analytic limits or all-body theorem.

Candidate integration: local commit `a03655dd`; significance integration: `5424232f`. This acceptance record and I50 integration receive a separate commit. [Publication instructions and mapping](../../PUBLICATION.md) describe the project-only filtered public history.
