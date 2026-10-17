# Family298: the noise-persistence interface remains unpaid

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

This is a pre-freeze obstruction record, not a theorem candidate or a negative theorem about the proposed phenomenon. No target was frozen. The pinned source is accepted as stipulated; it is not being audited.

## Exact operation supplied by the source

Write V_u=C+sqrt(u)S for its fixed large (p+1)-tuple, X=V_h, and A^(d) for uniform laws on a selected sequence of increasingly accurate cutoff microstate sets whose normalized volumes approach chi_R(X). Sections 5–6 keep those same ensembles throughout. With GUE noise of variance t, their two estimates read

    liminf H_d(A^(d)+sqrt(t)G^(d)) >= chi_R(X) + (1/2) integral_0^t Phi*(V_(h+s)) ds,
    limsup H_d(A^(d)+sqrt(t)G^(d)) <= L(h+t)-1.

The cumulant estimate makes chi*(V_(h+t)) >= L(h+t)-1/2 at the selected second noise scale. Combining the two inequalities transports the deficit backwards to X. The source never needs to identify the selected terminal entropy with chi(V_(h+t)).

The selected terminal law has the correct limiting moments. That fact alone supplies no reverse entropy comparison with the maximal volumes of all terminal microstate sets. An upper bound on one approximating ensemble's entropy cannot upper-bound a supremum over possible approximations. To prove a strict terminal gap, an additional maximality or exponentially sufficient coverage assertion is needed. To prove eventual equality, one instead needs a new class of entropy-maximizing models, or a suitable regularity/transport theorem. Neither follows from these two inequalities.

## The persistent block witness has a finite scale budget

For fixed p, the first p coordinates initially have block energy exceeding p/2. Projected additional noise has expected squared norm at most 2t. The actual proof bounds its probability of exceeding squared norm p/16 by 32t/p. The reference-Gaussian union-bound exponent, apart from o(d^2), is

    2 log(1+128 sqrt(v)) + log 2 - p/(256 v),  v=1+h+t.

Both steps are used at a scale t substantially smaller than p. With this one fixed tuple, the displayed estimates cease to pay the required margins as t tends to infinity. Increasing p with t changes the tuple and is not all-time persistence for one tuple. Scaling the tuple to accommodate an arbitrary prescribed finite horizon is likewise a standard parameter transfer, not a new mechanism.

This proves a limitation of the displayed mechanism, not disappearance of the entropy gap.

## Comparison with actual primary proof operations

Guionnet–Shlyakhtenko, Free Monotone Transport, arXiv:1204.2182v3, Theorem4.2/Corollary4.3, requires a conjugate-variable representation by convergent noncommutative power series with a small analytic norm. The proof reconstructs a cyclic-gradient potential and solves the analytic transport equation. Corollary4.6 then applies a change-of-variables formula to compute microstates entropy. The pinned source's ambient Wick testing and conditional expectation give L2 score control and a numerical Fisher deficit. They do not provide the analytic representation or its coefficient norm. The external analytic hypothesis cannot be silently replaced by the L2 estimate.

Jekel, An Elementary Approach to Free Entropy Theory for Convex Potentials, arXiv:1805.08814v2, Theorem7.1, assumes convex potentials with a dimension-independent semi-concavity bound, concentration and tails, and approximation of their gradients by trace polynomials. Uniform strict convexity is not required by that theorem. Its proof propagates the potential and gradient approximation under Gaussian convolution, identifies classical Fisher information with free Fisher information, and then passes through de Bruijn's integral. The source provides a lower-semicontinuity Fisher comparison for the selected models, not the required equality or approximation of their matrix scores. The source's Gaussian smoothing does not itself establish convexity.

## A precise failed shortcut: cutoff plus Gaussian smoothing

Here is an elementary obstruction to deriving matrix log-concavity from a bounded operator-norm cutoff alone. It is not a counterexample to the pinned ensemble, which has additional structure.

For every even d let D_d be diagonal with d/2 entries R and d/2 entries -R, where R>0. Let A_d equal D_d or -D_d with equal probabilities, and let G_d be standard GUE independent of A_d. Both support points have operator norm R and exactly the same one-variable trace moments; thus these ensembles concentrate at one bounded noncommutative law. Set Z_d=A_d+sqrt(t)G_d for any fixed t>0.

Use the real Hilbert–Schmidt geometry Tr(UV). Write a=D_d and f for the density of Z_d. Directly expanding the two Gaussian densities gives

    log f(x) = const - (d/(2t)) ||x||_HS^2 + log cosh((d/t)<x,a>_HS).

For e=a/||a||_HS, the directional Hessian of minus log f at zero is

    D_e^2(-log f)(0) = d/t - (d/t)^2 ||a||_HS^2
                       = d/t - d^3 R^2/t^2.

It is negative whenever d^2 R^2>t. Consequently no fixed positive noise time, however large relative to R, guarantees log-concavity uniformly in d from an operator-norm cutoff and moment concentration alone. Smoothing provides an upper Hessian bound, but the posterior covariance term can destroy the lower bound. Source-specific symmetry or additional regularity would have to pay the missing estimate. This example is deliberately not offered as a new substantial result.

## Disposition

No eligible, complete nonroutine deduction was obtained in this screen. The exact unpaid interfaces are (i) maximal terminal microstates versus the retained ensemble for persistence, or (ii) dimension-uniform convex/analytic score control for an equality route. Small-time persistence, time rescaling, and entropy-deficit repackaging do not repair these interfaces and are not nominated. The larger campaign may continue elsewhere without treating this screen as an accepted result.
