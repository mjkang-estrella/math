# I200: positive quadratic regularization of the Hankel cone

2026-10-12. **UNRESOLVED; NO SUBSTANTIAL NOMINATION.** Eight substantial findings remain accepted; two remain. The specific small-positive-delta nonliftability question is neither proved nor refuted. Two independent routes were completed to precise gaps. This is an unsealed research record; both independent acceptance gates remain with the parent.

The fixed data are exactly the family-095 Hankel construction at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, including the chosen basis matrix U and the Euclidean coordinates of y. Write g=eta^(-2)P_(w-perp)-ww^T and

    Q_delta(y)=U^T G(y)gG(y)U+delta||y||^2 I_r.

No change of basis or of perturbation is implicit. The source defines K_delta by its determinant construction and proves its hyperbolicity. The [analytic record](../experiments/i200_regularized_cone/analytic-attempt.md) supplies complete proofs of the following auxiliary results and explains their contribution limits.

## Exact conclusions for this family

There is a finite, explicitly specified constant sigma>0 such that **K_delta is spectrahedral for every delta>=sigma**, including the endpoint and the entire singular boundary. Let G_i=G(e_i), L=[G_1 U | ... | G_m U], and

    C=L^T g L,     sigma=-lambda_min(C).

The matrix C is a positive semidefinite matrix minus one rank-one matrix. It has exactly one negative eigenvalue, and

    0<sigma<=||L^T w||^2.

For delta>=sigma, factor C+delta I to obtain a joint linear Gram factor of Q_delta. Its skew-block Schur pencil represents K_delta exactly, with size at most (r+1)(mr+1). In particular delta>=||L^T w||^2 is a sufficient range requiring no spectral threshold. This bound is symbolic; no coefficients or eigenvalues were numerically computed.

There is also an attained threshold 0<delta_SOS<=sigma for existence of *any* joint linear Gram factor: that factor exists exactly for delta>=delta_SOS. Consequently K_delta is spectrahedral throughout that range. For 0<delta<delta_SOS, only failure of joint linear Gram factorization is established. **Failure of that factorization does not exclude a finite affine semidefinite lift.** The finite-dimensional compactness proof concerns fixed bilinear monomial Gram matrices only and gives no quantitative bound for arbitrary lifts.

These statements are useful exact restrictions on a possible stability theorem. They use coefficient regularization and the source's existing Gram-to-pencil operation, so they do not constitute a ninth substantial finding.

## Route A: an exact feasible patch, but a positive moment defect

The old rank-N patch cannot survive positive delta. We constructed a new polynomial boundary patch instead. Put A_h(s)=M(s)M(s)^T+hI for fixed h>0 and D_h=det A_h. Then

    p_(delta,h)(s)=
       (D_h A_h, tr(adj(A_h)Q_delta(y_s)), D_h y_s)

is polynomial of degree at most 4r+4 and lies exactly in E_delta, the source's affine section/projection. This uses homogeneity to clear the rational graph denominator.

The repaired patch does not have the required negative moment defect. On A>0, let f_delta(A,y)=tr(A^(-1)Q_delta(y)). Its Hessian is positive definite transverse to the radial direction at every y!=0: the added term satisfies

    (1/2)D^2(||y||^2 tr A^(-1))[(H,z)]^2
      =sum_j ||A^(-1/2)(z_j I-y_j H A^(-1))||_F^2,

whose kernel is exactly R(A,y). The source supplies convexity of the remaining term. The normalized evaluation coordinates y_s make the patch derivatives nonradial. For every normalized strictly positive moment functional, its tested trace residual is therefore **positive at order epsilon^2**, by an explicit covariance-Hessian formula. It cannot reproduce the negative epsilon^4 obstruction.

For fixed delta, shrinking the full-rank floor h to zero with bounded unscaled t is itself impossible: t>=delta(r-N)||y_s||^2/h. Sending h or delta to zero along with epsilon changes the source's order of quantifiers. The source's analytic selection on an open patch supplies neither an extension to the resulting singular stratum nor uniform Taylor constants. The precise gap is a new obstruction at y=0 and singular A with valid center-selection control, or a genuinely different nonliftability method.

## Route B and the smoothness check

The constructive route succeeds above the coefficient-Gram threshold and stops below it. Pointwise analytic square roots, piecewise positivity certificates, and finite approximations of angular factors do not by themselves produce a joint affine pencil. The 23-variable Choi-Lam companion closes such a gap with an exact bounded-degree matching identity, including indefinite test matrices and the range condition at singular X. No corresponding identity for the Hankel Q_delta was obtained.

The whole K_delta remains nonsmooth for every delta>0. At y=0 it contains the exact section X>=0,Z>=0. At X=diag(0,0,1,...,1), Z=I, the distinct supporting hyperplanes X_11=0 and X_22=0 rule out a smooth local defining inequality. Thus positivity of Q_delta away from zero does not meet a global Nash-smoothness hypothesis. The relevant primary results of [Netzer–Sanyal](https://arxiv.org/abs/1208.0441v1) and [Scheiderer](https://arxiv.org/abs/2509.17121v1) do not decide this family. Their positive approximation results do rule out blanket claims that smoothing preserves nonliftability.

## Evidence and scope

The [literature record](../sources/i200_regularized_cone/literature.md) gives the primary comparisons and exact reading limits. The [reading/failure log](../experiments/i200_regularized_cone/reading-and-failures.md) records the failed shortcuts. The [authentication record](../experiments/i200_regularized_cone/input-authentication.json) supplies hashes, pinned corpus URLs and reading scopes. The source's actual cone, separation, moment and analytic-selection operations were read; the accepted seed certificate was not replayed. The Choi-Lam matching/lift proof was inspected as a distinct constructive comparison.

Only authorized I200 outputs and one full-read external source copy were written. No I199/I201 outputs, ancestors, indexes, I31, staging, commits or publication were touched. No agents, research code, numerical scans, experiments, tests, snapshots, seals or historical replays were used. I198's g+tau I threshold and epsilon^12 estimate were not re-nominated. The unresolved interval remains 0<delta<delta_SOS, with no claim that its cones are all liftable or all nonliftable.
