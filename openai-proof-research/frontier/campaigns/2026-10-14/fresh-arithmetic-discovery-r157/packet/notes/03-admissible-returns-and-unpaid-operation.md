# Admissible returns, cusp accounting and the unpaid operation

PREFREEZE / no nominee. The finite-volume question in Note 01 is neither proved nor disproved. No theorem was frozen. The reductions in Note 02 are supporting calculations, not a weaker replacement offered for acceptance.

## 1. A fixed good peak need not have the source's compact-normalized ray

This distinction already occurs in the symmetric one-dimensional model, so it is not a counterexample to the desired finite-volume classification.

Use the upper half-plane H with its hyperbolic metric, and Gamma=PSL_2(Z). Its standard fundamental region

    {|x|<=1/2, x^2+y^2>=1, y>0}

has area

    integral_{-1/2}^{1/2} integral_{sqrt(1-x^2)}^infty dy dx/y^2
      = integral_{-1/2}^{1/2} dx/sqrt(1-x^2) = pi/3.

The discrete action is proper, with finite stabilizers. Scaling the metric to the chosen Einstein normalization only changes this finite area by a fixed factor. A finite-index torsion-free subgroup would give the same phenomenon, but is unnecessary because the question already allows orbifold quotients.

For gamma represented by an integer determinant-one matrix (a b;c d),

    Im(gamma z) = Im z / |cz+d|^2.                       (4)

At z=i this is 1/(c^2+d^2)<=1. More generally, if K is any compact subset of H, put

    a_K = min_K Im z > 0,   b_K = max_K Im z < infinity.

For c!=0, (4) is at most 1/(c^2 Im z)<=1/a_K. For c=0, d=+/-1 and it is at most b_K. Therefore

    sup Im(Gamma K) <= max(b_K,1/a_K) < infinity.        (5)

No sequence iY_j with Y_j tending to infinity can be written gamma_j k_j with all k_j in a compact K. Its image in the quotient goes arbitrarily far into the cusp.

Now conjugate by the Cayley map C(z)=(z-i)/(z+i), sending H to the bounded semialgebraic disk and infinity to p=1. The normal ray C(iY)=(Y-1)/(Y+1) is a radial approach to this smooth good supported point. Equation (5) says the precise compact normalization used by the source is unavailable along that ray for this finite-volume action. Nevertheless translations gamma_j(z)=z+j give gamma_j(i)=j+i tending to infinity, so C(gamma_j i) tends to p. Thus ordinary peak recurrence holds exactly as the envelope predicts.

The rates can be calculated, not merely described:

    zeta_j = C(j+i) = j/(j+2i),
    1-zeta_j = 2i/(j+2i),
    |1-zeta_j| = 2/sqrt(j^2+4),
    1-|zeta_j| = 1 - j/sqrt(j^2+4) ~ 2/j^2.             (6)

The tangential displacement is of order j^-1 and the normal depth of order j^-2. At the fixed center p, choosing t_j comparable to the normal depth makes the scaled real-normal coordinate unbounded; choosing t_j comparable to the total displacement gives a limiting point on the model boundary. This is the actual loss in (A), not a failure of ordinary orbit accumulation.

This example does NOT show that no other good point has admissible returns. Nor does it obstruct a moving-center argument; the disk is already symmetric. It specifically refutes the shortcut “the envelope gives the source's compact-normalized ray at the selected peak.” A sufficient continuation must select an appropriate point and sequence, or construct compatible changing charts, rather than claim this for every peak.

## 2. The source's joint limit does not itself prevent approach along a cone face

Consider even the constant semialgebraic normal-offset family

    A_s = (0,infinity)^2,
    F = R^2 \ (0,infinity)^2,
    d_*(v) = min(1,v_1,v_2) on the positive quadrant.

The joint parameter-limit conclusion is exact here. Take interior offsets

    v_j=(epsilon_j,epsilon_j^2), epsilon_j down to zero.

There is no scalar t_j for which both coordinates of v_j/t_j remain bounded above and bounded away from zero. Their ratio is epsilon_j, independent of t_j. At t_j=epsilon_j, the residual converges to (1,0) in F; at t_j=epsilon_j^2, its first coordinate diverges. Noncollapse says that the cone has an interior, not that every chosen sequence stays in it after a single scalar normalization.

In the product-half-plane model a separate dilation in each factor repairs this immediately. That repair is already consistent with the primary product-of-balls theorem. It is not a universal construction for an arbitrary semialgebraic boundary: the source's quadratic reduction uses ONE common normal weight and tangential square-root weight. Independent normal rates can change which Hermitian components survive and can promote previously discarded Taylor terms.

For example, with normal weights (t,t^2) and a tangential variable initially scaled by sqrt(t), a cubic tangential term divided by the second normal weight has size t^(3/2)/t^2=t^-1/2. It no longer tends to zero. Rechoosing the tangential weight can remove that divergence but may erase a previously nondegenerate Hermitian component. The calculation shows why the fixed quadratic truncation cannot simply be reused after declaring “allow multiple scales.” It is a local bookkeeping obstruction, not a domain with a claimed finite-volume quotient.

Semialgebraic curve selection in the ambient set does not select a suitable orbit sequence. The group action and orbit are not assumed semialgebraic. Replacing gamma_j q by a semialgebraic curve can destroy the compact normalization which the whole argument is trying to obtain. The source's ramification theorem applies to the geometric offset functions; it does not make arbitrary automorphism sequences definable.

## 3. The strongest alternative flow construction was compared at its operative step

KLW's Sections 6–7 avoid prescribing a normal ray in a convex domain. Their normal-bundle integral locates a complex extreme point p with totally real normal span V. The peak envelope supplies gamma_j(o)->p. For every supporting unit normal theta they retain the affine gap

    s_theta(x)=h_K(theta)-<theta,x>,
    exp(-2 d_U(x,y)) s_theta(x) <= s_theta(y)
        <= exp(2 d_U(x,y)) s_theta(x),
    dist(x,partial U)=min_theta s_theta(x).             (7)

Let delta_j=dist(gamma_j(o),partial U). For v in V-perp their contradiction argument over ALL supporting directions proves, for x_j=gamma_j(z_*),

    s_theta(x_j+t delta_j v) >= c delta_j/2
    for every theta and every |t|<=T,                  (8)

where c=exp(-2d_U(o,z_*)). Membership in the domain follows from the intersection of all supporting half-spaces. Their rescaled fields

    Z_j(z)=delta_j [D gamma_j(z)]^{-1}v

are locally bounded. A normalized supporting holomorphic function H_j satisfies

    dH_j(Z_j)=-ell_{nu_j}(v),
    limit dH(Z)=-i|v|^2 != 0,                           (9)

so the limit field does not vanish. Equation (8) bounds the Kobayashi lengths of the entire translated segments by 2T|v|/c. Properness of convex-domain Kobayashi balls then traps the pulled-back trajectories for every finite T and proves completeness. All of this is paid primary work, including the full trajectory estimate; no “nonzero limit field implies complete” shortcut is taken.

The source's finitely many nonlinear peaks do not give the all-support membership identity in (7). Their independent differentials and O(t) values control coordinates when a noncollapsed scalar normalization is already present. They do not, on their own, bound every possible additional boundary gap along x_j+t delta_j v. Even a finite set of support gaps at one point can miss a much smaller gap near a moving boundary face. For the elementary parabola region y_1>0, y_2>y_1^2, the point (epsilon,epsilon^2+epsilon^M), M>2, has distance of order epsilon^M to the parabola, while its two coordinate gaps at the origin have orders epsilon and epsilon^2. Convex theory repairs this by retaining the entire varying support family. This local real example is used only to test a proposed inference from finitely many gaps; it is not claimed to satisfy the full complex quotient question.

Thus importing the complete-flow route requires an actual replacement for (7)–(8), including domain membership along trajectories, and a compatible global structural conclusion. KLW's HHR splitting cannot be invoked by assuming uniform squeezing and contractibility that the present hypotheses have not yet supplied. Its actual convex theorem and Pu–Wang's actual piecewise-smooth theorem are already credited, rather than offered as partial nominees.

## 4. Exact remaining construction

The strongest closed reduction consists of:

* the source's generic semialgebraic boundary preparation and actual included balls, with Stein hulls replacing its cocompact disc-continuity argument;
* finite-volume holomorphic/PSH orbit envelopes giving ordinary returns, including the orbifold case through the complete KLW lemmas;
* the global forward/inverse scaling construction under the explicit compact-normalization interface (A), with a local Jacobian/inverse-stability argument eliminating the apparent need for proper Kobayashi balls;
* the conversion of the resulting quadratic epigraph into a true Siegel domain by Steinness and rotational discs, followed by the actual finite-volume frame-lattice argument and the Vey graded trace calculation.

What is not constructed is a good-point/sequence selection or a moving-center, multiple-scale normalization which, for EVERY U and Gamma in Note 01, supplies a noncollapsed interior anchor, locally bounded forward maps, two-sided included/excluded-set convergence, and compatible complete symmetry-producing operations. The scalar fixed-point form (A) is a sufficient route, not asserted to be necessary for classification. An alternative complete-flow route must supply its own all-boundary trajectory retention and structural hypotheses rather than presume them.

The cusp and two-scale calculations explain why the ordinary-envelope and nonempty-cone conclusions do not supply those interfaces automatically. They do not establish a counterexample to the full finite-volume question, a no-go theorem for moving centers, exhaustion of methods, or a worldwide novelty claim. No smaller convex, piecewise-smooth, complete-hyperbolic, HHR, or conditionally normalized theorem is nominated. All old targets and dispositions remain immutable.
