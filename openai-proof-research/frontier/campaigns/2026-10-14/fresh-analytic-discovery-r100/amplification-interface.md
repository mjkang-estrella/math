# Amplification tests for the unchanged all-deficit target

Live author derivations. The completed small-deficit theorem and frozen scope are unchanged. The question is whether a log-concavity-preserving operation can turn an arbitrary absolute deficit into a small one while retaining enough quantitative information to recover the original product-exponential approximation. No projection entropy superadditivity is assumed.

Write the affine-invariant deficit as

 Delta(X)=h(X)-n-(1/2)log det Cov(X).

For centered isotropic X this is the frozen delta. All calculations below are exact, on the stated integrability class. They are not new candidate theorems or independent review.

## 1. Convex epigraph extension: exact normalized deficit

Let X have density Z^(-1)exp(-V(x)) on its convex support, where V is convex, X is centered isotropic, and V(X) has finite second moment. An additive constant in V is irrelevant. Let E be an independent mean-one exponential and define

 T=V(X)+E.

The joint density of (X,T) is Z^(-1)exp(-t)1_{t>=V(x)}. Its support is a convex epigraph and its potential t is affine on that support, so the joint law is log-concave. The triangular map (x,e)->(x,V(x)+e) has unit Jacobian in the conditional-density sense; no differentiability of V is needed. Therefore

 h(X,T)=h(X)+1.

Set b=Cov(X,V(X)) and sigma²=Var(V(X))-|b|²>=0. The covariance Schur complement of the X block is 1+sigma², hence

 Delta(X,T)=delta-(1/2)log(1+sigma²).                 (1)

In particular this operation really CAN lower the normalized absolute deficit; the reduction is not the superficial division by dimension. Its size is determined by the nonlinear regression variance sigma², not by a freely chosen scale.

Replacing T by V(X)/a+E/a for any a>0 changes entropy by -log a and covariance determinant by a^(-2); these cancel exactly in Delta. Thus changing the epigraph slope/height does not provide a tunable amplification parameter.

The source theorem applied to this extension implies delta>=(1/2)log(1+sigma²). That is a consequence of its stipulated entropy inequality, not an independent proof of a reverse bound. In particular no lower bound on sigma² in terms of exp(2delta)-1 is available here.

## 2. All nonnegative split epigraphs: no gain from extra dimensions

More generally let a_i>=0, sum_(i=1)^k a_i=1, and let E_i be independent mean-one exponentials, independent of X. Define T_i=a_i V(X)+E_i. The joint density is

 Z^(-1) exp(-sum_i t_i) product_i 1_{t_i>=a_i V(x)}.

The support is convex and the density is log-concave. Conditional entropy is k. The covariance Schur complement is I_k+sigma² aa^t, so the matrix determinant lemma gives exactly

 Delta(X,T_1,...,T_k)=delta-(1/2)log(1+sigma²|a|²).    (2)

Since |a|²<=1, no split extension reduces the deficit more than the single epigraph. Equal splitting gives |a|²=1/k and the improvement tends to ZERO as k grows. Different positive exponential rates are absorbed by invertible coordinate rescalings and lead to the same formula after normalizing the coefficients to sum1.

This calculation rules out deficit dilution by adding many independent epigraph heights in this natural convex class. It does not rule out every possible higher-dimensional construction.

## 3. Iterating the canonical extension stalls immediately

After one epigraph extension the negative log density, apart from a constant, is the AFFINE coordinate t on its convex support. Its regression residual against the full vector (X,T) is zero. Thus a second canonical epigraph extension has sigma²=0 in (1) and leaves Delta unchanged. Indeed the second added height is T+E', an invertible affine transform of the previous vector together with an independent exponential. Repetition has the same property. Whitening or another invertible affine change between steps does not alter this conclusion: the potential remains affine on its transformed support.

Consequently neither iterative canonical epigraphs nor their split versions can successively shrink the deficit to the small-absolute-deficit threshold.

## 4. Explicit all-dimensional test: Gaussian input

For standard Gaussian X in R^m take V(x)=|x|²/2. Then b=0, sigma²=m/2, and

 delta=c_G m,  c_G=(1/2)log(2pi e)-1>0,
 Delta(epigraph)=c_G m-(1/2)log(1+m/2).               (3)

This tends to infinity linearly. Thus even the maximal reduction within (2), followed by any number of canonical epigraph extensions and affine normalizations, fails to enter the small-deficit regime for Gaussian inputs in large dimension. This is a counterexample to the proposed amplification operation, not to the frozen stability theorem: the latter permits an O(m) cost when delta is proportional to m.

The same obstruction occurs in the ACTUAL intermediate regime, not only when delta is proportional to the total dimension. Take k independent standard Gaussian coordinates and m-k independent centered mean-one exponentials. The total deficit is c_G k. Its potential is the Gaussian quadratic plus an affine sum of the exponential coordinates on the product support. Affine regression removes that entire sum, leaving sigma²=k/2 exactly. Thus the best split-epigraph deficit is c_G k-(1/2)log(1+k/2). Choosing k tending to infinity with k/m tending to zero gives delta tending to infinity but delta/m tending to zero, while the lifted deficit still never enters the small absolute regime. This family already satisfies the desired stability bound by its explicit product structure; it is solely an obstruction to the proposed amplification.

The test also explains why dividing an entropy gap by the enlarged dimension is irrelevant. The proved stability premise is an absolute deficit bound, not a normalized per-coordinate one.

## 5. Interpolation and smoothing do not automatically transfer the ratio

Gaussian convolution and isotropic Ornstein–Uhlenbeck interpolation preserve log-concavity, but a standard Gaussian input remains standard Gaussian after isotropic normalization. Its absolute deficit is c_G m. Hence these operations cannot universally reduce the deficit to zero.

Geometric density interpolation f_s proportional to f^s g^(1-s), where g is an exponential product on a cone, preserves log-concavity when defined. However support is the intersection for every 0<s<1. For a compactly supported f, the s down to0 limit is the exponential law restricted to that compact support, not the full equality density. For example f uniform on [0,1] and g(x)=exp(-x)1_{x>=0} give the limiting truncated exponential proportional to exp(-x)1_[0,1]. After isotropic normalization it remains compactly supported and cannot be an equality law; the source's equality characterization makes its deficit strictly positive. There is no arbitrary small-deficit endpoint from this interpolation for this fixed input/support.

Other convex-potential interpolations that expand support may reach an equality law, but small-deficit stability then controls only the endpoint neighborhood. To infer the original estimate one still needs a quantitative reverse comparison preserving W2²/delta along the path. Log-concavity of the path by itself provides no such comparison. No such reverse inequality is asserted here.

## 6. An additional lifting issue even if the deficit were small

Whitening the epigraph extension preserves X as an orthonormal-row linear projection of the normalized enlarged vector, because Cov(X)=I. W2 contraction therefore transfers an enlarged product approximation only to a projection of a rotated (m+k)-dimensional exponential product. Such a projection is not generally an m-dimensional rotated exponential product. For instance (E_1+E_2-2)/sqrt2 is an isotropic one-dimensional projection of an exact two-dimensional equality law, but its gamma-shaped density is not an exponential up to reflection/translation. Thus the target family is not closed under orthogonal-row projections.

Any successful extension amplification must solve BOTH the absolute deficit reduction and this equality-family recovery problem. Equations (1)-(3) rigorously delimit the canonical epigraph route; they do not establish a full impossibility theorem for localization or every convex extension.

## Reading and status

These are direct original calculations using the already-read source affine entropy convention and equality classification. No new external primary theorem is invoked and no claim of literature novelty is made. The proof uses only the finite-second-moment condition on V for the exact regression formulas; Gaussian and uniform/truncated-exponential tests satisfy all needed integrability. The full all-deficit target remains unresolved. Parent and r102 retain the separate mixed-block route.
