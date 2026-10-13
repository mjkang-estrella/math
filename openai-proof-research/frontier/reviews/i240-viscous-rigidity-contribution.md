# I240 — independent contribution gate on finite-viscosity fitted-class rigidity

**Verdict: TECHNICAL. Do not accept as the tenth substantial finding.** The exact finite-positive-tau affinity theorem is not shown to be already known. It does go beyond the hypotheses of the classical globally Lipschitz argument. Nevertheless, relative to the full stipulated source package, the submitted proof is a useful technical extension assembled from the supplied extremal envelope and standard autonomous monotone-divergence comparison, with two elementary localization lemmas. It does not clear the requested independent substantial-contribution standard.

This judges importance, not truth. The separate I239 gate remains separate and was not read. I read the complete finalized proof and its reading/literature records. The requested proof SHA256 matches exactly: `a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931`. No accepted-count change is recommended, even if the proof gate passes. No claim of worldwide priority is made.

## Exact conclusion under review

For every m>=1, finite tau>0 and finite C0>=0, let V be a continuous entire viscosity solution of

    V_tt + 2 DxV.DxV_t + DxxV[DxV,DxV] + tau Delta_x V = 0.

Upper C2 tests satisfy the displayed operator >=0; lower tests satisfy <=0. At every center (x,t) and every R>0, suppose some p,a give

    |V(x+h,t+l)-V(x,t)-p.h-(a-|p|^2/2)l| <= C0 R
    for |l|<=R and |h-p l|<=R.

The candidate concludes V is affine, without assuming any derivative or global gradient bound. It is qualitative at each fixed tau. The fixed-drift result, with the naturally drifted shear and time coefficient, is a change-of-variables corollary of this same statement.

## The globally Lipschitz objection does not dispose of the theorem

The classical argument is valid under its actual extra hypothesis. If V is globally Lipschitz in all variables, its flux

    a(p,q)=exp((q+|p|^2/2)/tau)(p,1)

has a Jacobian uniformly positive definite on the bounded full-gradient range. Each translation difference V(z+h)-V(z) is bounded and solves a linear divergence equation with measurable symmetric uniformly elliptic coefficients obtained by averaging Da between the two gradients. Scale-invariant linear Harnack/oscillation decay makes every such difference constant; continuity and additivity then make V affine. No smooth differentiation of V is necessary. The exact linear hypotheses are in [Crescimbeni–Forzani–Perini, Sections 2–3](https://ejde.math.txstate.edu/Volumes/2007/38/crescimbeni.pdf).

But FIT alone does not give that bounded full-gradient range. The smooth function V(x,t)=x1 sqrt(log(e+x1^2)) has FIT with C0=10 at every center and radius and has unbounded horizontal derivative. The full all-shear verification is reproduced in the [contribution analysis](../experiments/i240_viscous_rigidity_contribution/contribution-analysis.md). It is not a PDE solution, and I do not use it as one. It proves the geometric implication is false. Requiring a non-Lipschitz PDE+FIT example would be inappropriate, since the candidate's conclusion excludes one. The analytic gap is real: no older theorem read here supplies a global derivative bound from this FIT hypothesis, and source growth O(R log^2 R) is not linear growth.

Likewise, the actual older Liouville statements do not identify the candidate as KNOWN. [Peletier–Serrin, printed pp. 66 and 68](https://www.numdam.org/item/ASNSP_1978_4_5_1_65_0.pdf), require bounded gradients in the relevant entire-solution theorems; their homogeneous quasilinear corollary also imposes one-sided sublinear growth. Those are not this continuous, logarithmic-growth, sheared-fit class. No REG_tau estimate is presumed to erase the distinction.

## What is supplied, and what I236 adds

The pinned [sections 03–05](https://github.com/openai/math/tree/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/Uniform-Interior-C1alpha-Estimates-for-Infinity-Harmonic-Functions-October-4-2026/build/manuscript/sections) already supply the exact FIT class, frame normalization, dyadic fit estimates, compactness, subquadratic tails, barycentric envelope, spatial semiconcavity, extremal Jensen quotient, measure attainment, and positive-gap contact pair. These were read as source contracts and treated as free, not as new discoveries. The exact family path inventory lists one manuscript and no same-family viscous companion; this bounded check is not an exhaustive literature search.

Adding the common horizontal translation directions to the source's common-time matrix inequality transports the tau trace through the barycentric envelope. The variance is constant in those directions. This is a legitimate compatibility calculation, not an independently new envelope mechanism. The affine-slice case is repaired by an elementary midpoint-in-time identity from FIT, followed by the given growth bound and c''=0.

The final contact mechanism is different from the source's homogeneous discrete propagation. I236 does not pretend that its failed finite-slope and stochastic inequalities survive. Its new steps are:

1. A supporting spatial quadratic with slightly enlarged curvature localizes a spatial maximum h(t). The PDE applied to a scalar upper test of h gives h''>=-C. Elementary convex chord bounds and reversal of the base time yield time Lipschitz continuity of the spatially semiconcave subsolution. This is the best equation-specific observation, but is an elementary partial-regularity lemma; it gives no uniform REG_tau bound for arbitrary V.
2. A steep full-space cone infimum of the continuous supersolution preserves the viscosity inequality by translation. The strict inequality between cone slope and the subsolution's Lipschitz constant both preserves contact and recovers contact with the original function. This is a useful exact detail in standard infimal-convolution localization.
3. Once both functions are locally Lipschitz, the autonomous convolution/Alexandrov/Fatou passage is an adaptation of the established [Julin–Juutinen method, Section 3](https://arxiv.org/abs/1104.2197v1). The explicit smooth monotone flux makes this adaptation simpler than singular-gradient weak-equivalence problems. The averaged Jacobian and linear weak-solution Harnack then give contact propagation. The harmonic replacement and boundary-trace argument correctly match the reference's solution hypotheses; they do not introduce a new Harnack principle.

The resulting local contact theorem is the strongest ancillary statement actually present: in any connected open set, a continuous spatially locally uniformly semiconcave subsolution below a continuous supersolution has either strict separation everywhere or equality everywhere. Its intermediate form assumes only that the subsolution is locally Lipschitz. This is worth preserving as a technical lemma. It is not, on the evidence here, a separate substantial finding, and it is not an additional count alongside affinity.

## Why the combination still does not pass this gate

The combination solves a genuine interface problem, but its global structure is furnished by the stipulated source and its local analytic engine is the known strictly monotone flux. The added steps are supporting-quadratic localization, scalar semiconvexity, steep-cone regularization and bounded-gradient passage to a standard linear equation. They need careful checking; their correctness and their utility are not equivalent to independent substantial novelty. There is no new quantitative estimate for the fitted solutions, new asymptotic control, or new global propagation mechanism once the source contact construction and classical local comparison are supplied.

I therefore do not describe this as the unchanged homogeneous proof, nor dismiss it merely by asserting uniform ellipticity. It is a completed technical transfer using a different, classical terminal argument. That is the narrower, supported reason for the negative contribution verdict.

The equation and exponential flux already occur in [Sánchez Morgado, (EL), (4), (7)](https://arxiv.org/abs/1712.10275v1) and [Porretta, (1.7)](https://arxiv.org/abs/2203.04856v1), with the latter using the opposite potential sign. Their periodic smooth or prescribed-positive-marginal results do not state this fitted theorem. Trudinger's Hessian-independent gradient-Lipschitz condition was checked directly and is not satisfied by G_tau. The [Ohnuma–Sakaguchi warning and mean-curvature-specific theorem](https://arxiv.org/abs/1806.03587v1) remain respected. None of these comparisons licenses a generic strong-comparison shortcut, or certifies worldwide novelty by absence.

## What this advances

It removes the finite-positive epsilon/lambda limiting obstruction, conditional on obtaining the actual limit and all its FIT hypotheses upstream. It does not prove the required p-family compactness/regularity, p-to-infinity gradient convergence, or a tau-uniform result. The infinite-tau divided PDE is only Delta_x V=0 and still admits V=sin t under FIT. The broader local contact lemma is not a named-open-problem resolution on its own.

The record should therefore retain this as a useful finite-tau technical result if correctness passes independently, while continuing the search for the tenth substantial finding. Detailed primary-source hypotheses, the positive case for acceptance and the reasons it falls short are in the [analysis](../experiments/i240_viscous_rigidity_contribution/contribution-analysis.md); [reading limits](../experiments/i240_viscous_rigidity_contribution/reading-and-failures.md), [literature](../sources/i240_viscous_rigidity_contribution/literature.md), and [authentication](../experiments/i240_viscous_rigidity_contribution/input-authentication.json) accompany it.
