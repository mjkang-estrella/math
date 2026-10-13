# I264 derivation map

The complete proposed proof is in `frontier/iterations/i264-weighted-neighborhood-channel-stability.md`. This is an unreviewed strengthening of one existing spectral nomination, not a new accepted finding.

The exact difficulty with removing essential-supremum control is that the first-channel coupling Q(w|f|² phi) need not be a fourth-order term relative to J. A pointwise Taylor expansion from I262 is insufficient. I264 instead retains both Feshbach coupling components and controls the first by a dual Sobolev estimate: B1<=K J integral w|f|²<=K C1 J^(3/2). The transverse coupling uses g=sqrt(1-|f|²)f and exact principal-channel centering. The favorable difference J-integral w rho|g|² supplies the large-angle contribution.

All operator perturbations are bounded in form norm relative to the compressed H0+a², through integral ||U||<=C1 sqrt(J). This is dimension independent and proves spectral isolation directly without analytic continuation. The threshold tail is controlled by the known operator-valued endpoint theorem followed by two weighted Holder inequalities. The second gives integral sqrt(w)|f|²<=Ctheta J^theta; it replaces the essential-supremum factor.

The constants are specified in the full proof. Their finiteness uses r>1, so no endpoint extension is claimed. The upper bound follows from the ground-state test, while the lower bound requires the compressed spectral comparison and the full threshold-moment tail. The conclusion assumes J small; no inference from D small to J small is made.

## Analytic checks at large-angle defects

These are deductions from the proposed estimates, not independent review or numerical experiments. They identify genuine examples covered by the new statement but excluded from essential-supremum-small charts.

Let A be an interval and choose v=e2 on A and v=e1 on its complement. For J_A=integral_A w rho<Z/2, the principal channel is e1, so J=J_A exactly, f=1_A in the second channel and g=alpha f=0. The essential supremum distance to every constant projector is bounded away from zero as long as both A and its complement have positive measure. The operator splits as (h+w1_A) direct-sum (-d²-w1_A); this uses a sharp, discontinuous orientation, which is allowed.

Let L_A=integral_A w. Equations (5)--(7) of the proposed proof give, whenever J tends to zero,

    0<=J-delta<=K J L_A/(1-t),
    t=K C1 sqrt(J)+J/a².

Here B2=0 and only the first-channel coupling remains. If L_A tends to zero, delta/J tends to one. The endpoint estimate bounds all negative moments of the second block by (L_A/2)^(2gamma). Thus if L_A^(2gamma)=o(J), the exact deficit satisfies

    D/J -> gamma a^(2gamma-2).

For A=[L,L+1], L tending to positive infinity, sech asymptotics give

    J asymptotic to a positive constant times exp(-2a(r+1)L),
    L_A asymptotic to a positive constant times exp(-2raL),
    L_A^(2gamma)/J = O(exp(-2aL)) -> 0,

because 4r gamma=2r+4. Therefore arbitrarily distant orthogonal channel defects satisfy the proposed linear scale despite never being pointwise-small perturbations. The main proof's weaker power bounds accommodate this example.

For A=[0,ell], ell down to zero, continuity and positivity of w and rho give J asymptotic to w(0)rho(0)ell and L_A asymptotic to w(0)ell. Since 2gamma>1, L_A^(2gamma)/J tends to zero again. The same exact ratio follows for large-angle defects of shrinking measure in the core.

These examples rule out replacing the linear deficit scale by an asymptotic estimate D=o(J) throughout the neighborhood. They also force any uniform upper coefficient at infinitesimal J to be at least gamma a^(2gamma-2). The proposed M_gamma obeys this constraint, equaling it when gamma>=1. None of these checks establishes contribution novelty or replaces either independent gate.
