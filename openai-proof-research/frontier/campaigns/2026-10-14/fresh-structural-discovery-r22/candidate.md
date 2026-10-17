# Family334: accumulation and genericity screen

Status: **PRE-FREEZE — no substantial candidate nominated**. Counted=false. No original full target was frozen, and no weaker statement is being substituted for one. The mathematical findings below delimit which construction would still need to be paid. Myeongjin Kang, no affiliation. Original prose CC BY4; code MIT; third-party sources private.

## Exact source interface

At the stipulated pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, family334's sole catalog manuscript is *A Smooth Metric with No Local Isometric Immersion into Three-Space*. Its Theorem A supplies a C∞ positive metric h on (-1,1)² with no smooth R3 isometric immersion on any neighborhood of 0. Corollary `cor:flat-jet` adds j∞₀h=j∞₀I. This is stipulated source truth, not independently re-proved here.

The actual construction is stronger than this headline for screening purposes. Proposition `prop:patch` supplies a residual set of whole-square height obstructions within a fixed curvature-model perturbation space. All individual model-patch curvature zeros are clean sign changes. Section `assembly` already supplies arbitrarily small perturbations in any finite collection of seminorms, summable all-orders derivatives, two levels of accumulation, a finite rotation net, and a negative-disk boundary argument. It does not state local nonrealizability at every model-patch point. Its exact scoped objects, not a generic nonsolvable Monge–Ampere equation, must be retained.

## Paid supporting deduction: both behaviors are dense at a flat jet

Let X be the space of C∞ positive definite metrics g on D=(-1,1)² satisfying ∂ᵅ(g−I)(0)=0 for every multi-index α, equipped with the inherited compact-open C∞ topology. Let G be the subset locally smoothly isometrically immersible in R3 at 0 and B=X\G.

**Supporting proposition. Both G and B are dense in X.** This is a technical consequence, not a nomination.

Choose a smooth cutoff χ with values in [0,1], equal to 1 on the unit disk and 0 outside the disk of radius 2, and put χρ(x)=χ(x/ρ). For any g∈X define

    gρ,good = (1−χρ)g + χρ I,
    gρ,bad  = (1−χρ)g + χρ h,

where h is the source metric, restricted to a small disk as necessary. Both metrics are smooth positive definite by convexity of the positive cone, and both retain the Euclidean full jet at 0. The first equals I near 0, hence lies in G. The second equals h near 0 and lies in B: any local immersion of it would restrict to an immersion of h on a neighborhood of 0.

For completeness, if a smooth tensor f is flat at 0, Taylor's theorem applied to each ∂ᵝf says that for arbitrary fixed m,N there is C such that |∂ᵝf(x)|≤C|x|ᴺ for |β|≤m and sufficiently small x. Leibniz's rule therefore bounds every derivative of χρf of order at most m by C′ρ^(N−m). Taking N>m proves convergence to zero in every fixed C^m seminorm; compact sets away from 0 eventually see no change. Apply this to I−g and h−g. Thus both sequences converge to g in X, proving density.

This construction uses only source existence plus flatness and a standard cutoff. It supplies neither residuality nor measure-theoretic prevalence. Describing density as genericity would be incorrect.

## Necessary restriction on a prescribed bad locus

For any smooth surface metric g on D, let B(g) be the set of points admitting no smooth local R3 isometric immersion. Its complement is open by definition, so B(g) is closed. Classical smooth local existence at points of nonzero Gaussian curvature implies B(g)⊂{K=0}. If B(g) contained a nonempty open set U, K would vanish identically on U. A two-dimensional flat metric is locally Euclidean, yielding local planar immersions at points of U, a contradiction. Thus B(g) is closed and nowhere dense.

This rules out a dense bad-locus proposal outright. It is a necessary-condition screen, not a counterexample to the pinned theorem. The nonzero-curvature existence statement is recalled in Khuri2009's actual introduction; no sign-definite degenerate-curvature theorem is being assumed.

## Two precise unpaid operations

**Exact prescribed locus.** A possible research question, not a frozen assertion, is whether every closed nowhere-dense C⊂D can occur as B(g) for a smooth positive metric. A repeated source assembly may plausibly place obstruction clusters near C, but mere containment C⊂B(g) would use the existing summation operation and would not answer this question. Equality requires smooth local realizability at every point of D\C. The individual model patches have clean curvature zeros, but the infinitely flat disk boundaries and other accumulation points do not. Source `assembly` gives no local existence theorem there. This reverse inclusion is the unpaid operation. No assertion that arbitrary C is realizable, or that containment has been fully proved, is made.

**Full flat-jet genericity.** A second research question is whether B is residual in X. The source proves residuality only in a space of tensors supported in one central box with the exterior metric and curvature profile fixed. That affine slice has empty interior in the full flat-jet metric space. A residual subset of a closed thin slice need not be residual, or even dense, in the ambient space. The supporting proposition above establishes density by another argument; it still does not establish residuality.

To imitate the source's bounded-height Baire proof in X, one would need its cap/oscillatory estimates to remain uniform when exterior metric coefficients and the curvature profile also vary. The source's Proposition `prop:cap` is stated for the model setup; its use in `pulse` keeps the exterior fixed. Stability of the requisite directed multiplier and propagation under arbitrary ambient perturbations has not been supplied. Alternatively, a closed-class compactness argument for bounded C^m immersions gives a lower-regularity limit, while the stipulated source excludes smooth immersions. Passing from that limit to a smooth immersion without a suitable regularity theorem is unjustified. The source itself successfully avoids this compactness issue inside its constrained smooth-height classes; this screen does not mistake that for a defect in the source.

Neither unpaid operation currently has a demonstrated tractable mechanism beyond the already-paid construction. No scope is frozen merely to label the missing lemma a new result.

## Closest primary operations

[Nadirashvili–Yuan 2008](https://sites.math.washington.edu/~yuan/papers/2008CVPDE.pdf), read completely, constructs a C^{2,1} nonnegative-curvature metric excluding C² local embeddings. Its Steps 1–4 already use localized pieces, tails preserving curvature sign, rapidly decaying amplitudes, and an accumulation-point contradiction. This finite-regularity theorem is not a smooth-metric premise for this screen.

[Nadirashvili–Yuan 2002, v1](https://arxiv.org/abs/math/0208127v1), read at both theorem statements, the introduction, Section 2's final assembly, and Section 3's full displayed construction, states a stronger smooth nonpositive-curvature counterexample and a metric strictly negatively curved off its single bad base point. Section 3 already uses a diagonal small perturbation preserving divergence of bounded-regularity embedding norms. Hence single-point isolation and iterative compactness cannot be presented as new proof operations without addressing this antecedent. The pinned source explicitly notes a status discrepancy between this preprint and the later published accounts and leaves it unresolved. I preserve that discrepancy; I neither certify the older preprint's proof nor import its assertions as established premises.

[Khuri 2009](https://www.math.stonybrook.edu/~khuri/Khuri_AIMS_Darboux.pdf), read completely, already constructs accumulating flat curvature bumps, realizes curvature by an ODE, derives boundary nonvanishing of a covariant Hessian, and passes to solution-dependent coordinates. Its Theorem 1 is a reduction, with the required nonsolvable curvature profile explicitly unpaid there. A repetition of that reduction would not be a new construction.

These comparisons concern actual proof operations. A bounded search found no exact full-flat-jet residuality or arbitrary prescribed-locus theorem, but this is not a priority or nonduplication certificate.

## Disposition

Preserve the source-supported two-sided density deduction as technical, the closed-nowhere-dense restriction, and the two exact unpaid interfaces. No substantial candidate, independent PASS, count, manuscript, formalization or public action follows. A later return would need an actual stability/local-existence operation, not another accumulation-set or regularity parameter variant.
