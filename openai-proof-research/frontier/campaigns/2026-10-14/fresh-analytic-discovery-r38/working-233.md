# Full polarization target: operative attempt and exact unpaid interface

Myeongjin Kang; no affiliation. Original prose CC BY 4.0. The immutable target is original-scope-233.md. It is unproved; no narrower theorem is substituted.

## What is paid

Pinned233 proves the joint height and complete current-support limit for every fixed critical coupling and every Jordan domain. In its notation H_delta is integer on primal vertices, half-integer on dual faces, h=pi sqrt(g) H in the distributional limit, and

    tau_delta(v)=cos(pi H_delta(v)),
    tau_delta^dagger(f)=sin(pi H_delta(f)).

The wired boundary fixes the common spin sign. The exact edge representation makes current components carry independent fair polarization colors, except the fixed wired component. Consequently, for either respective boundary law,

    E[tau_delta(x)tau_delta(y)] = P(x and y lie in the same current component),   (1)
    E[tau_delta(x)] = P(x is in the wired boundary component)                   (2)

in the wired case, while the free mean is zero. These are exact finite identities; conditioning on the current and complementary spin configuration proves them immediately. Isolated vertices count as components. The diagonal in(1) is exactly1.

AL López–Sepúlveda2602.06011v2, section9.1, Lemma9.1, uses pre-existing Ising spin/disorder correlations to establish the marginal cos/sin chaos law and an integrable collision bound. Theorem9.5 then identifies its underlying GFF with the nesting-height limit by local-set inclusion, equal laws, and iteration. The complete excursion-measure argument following9.5 uses that field identification and the same collision bound to control small clusters. Remark9.2 explicitly asks whether cos/sin convergence can be obtained directly from the height without correlation formulas. Thus the new debt is already sharply identified in the primary body; merely repeating its later local-set argument would be technical.

ALHL2602.05886v1, Conjectures1.1–1.3 and surrounding text, supplies the exact critical-line predictions and explicitly anticipates robust transfer once the required inputs hold. Its Proposition1.13 and section5.3 already construct the continuum magnetization series for g<4. No alternative proof of that construction is proposed here.

## Quantitative kernel needed for the field

Write alpha=1/sqrt(g), x=alpha²/2, r_D(z)=CR(z,D), and q_delta for the reference disk one-point function in the scope. If normalized correlations converge with the expected continuum law, then at distinct interior points they must satisfy

    q_delta^(-1) E[tau_delta(z)] -> r_D(z)^(-x),
    q_delta^(-2) E[tau_delta(z)tau_delta(w)]
        -> (r_D(z)r_D(w))^(-x) cosh(alpha² G_D(z,w)),             (3)
    q_delta^(-2) E[tau_delta^dagger(z)tau_delta^dagger(w)]
        -> (r_D(z)r_D(w))^(-x) sinh(alpha² G_D(z,w)).             (4)

These formulas follow directly by expanding the real and imaginary parts of Gaussian exponential fields. Their diagonal singularity is |z-w|^(-alpha²), and alpha²<3/4 throughout the full target. This is integrable in two dimensions. For a useful sufficient discrete collision estimate on a compact K inside D one would want, for some gamma<2,

    q_delta^(-2) P(x connected to y) <= C_K (|x-y|+delta)^(-gamma),              (5)

together with the corresponding higher-point bounds and off-diagonal limits. The exact second moment of a normalized test is

    delta^4 q_delta^(-2) sum_{x,y} phi(x)phi(y) P(x connected to y).             (6)

Even its diagonal alone has order delta²/q_delta². A route through uniform second moments must control this term; the source's upper one-arm estimate q_delta<=C delta^a does not give the needed lower bound or normalized off-diagonal estimate. Equations(3)–(5) are targets for an interface, NOT deductions from the source theorem.

Conditional on (5), the variance contributed by components of diameter at most rho is bounded, using independent fair component signs, by the part of(6) with |x-y|<=rho. Summing annuli gives C rho^(2-gamma), uniformly up to the diagonal. This is exactly the type of small-cluster argument already used in the primary excursion proof. It is paid once(5) is supplied and earns no separate count.

## Attempted annular normalization and its actual failure

The proposed mechanism was to compare one-arm-conditioned current laws between concentric scales, use a regeneration event to forget the microscopic initial shape, and derive normalized one-point/two-point ratios from the limiting two-valued-set geometry. A successful version would need a uniformly contracting conditional kernel, or an equivalent ratio-limit theorem, for a distinguished surviving current arm. Fixed-scale unconditioned support convergence is not that theorem: the conditioning event has probability tending to zero as the inner scale reaches the lattice.

The source's available regeneration is Proposition comparison plus Proposition circuits in03-spatial. It orders (s,W^+,-W^-), where W is the EXACT complementary percolation, not the other current. A common monochromatic OPEN W circuit seals a flat chamber and permits identical sampling inside. Its lower bound is conditional on the permitted (s,W) exploration, not on a completed current-arm survival event.

Let A be the event that an N current arm crosses an annulus from its inner to outer boundary, and C the event of a complete W circuit separating those boundaries. Since every W edge crosses an N-closed edge, planarity gives A intersect C empty. Therefore P(C|A)=0 whenever P(A)>0. The source lower bound P(C|permitted past)>=p>0 cannot be retained after the proposed conditioning. The exact good event used for unconditioned regeneration disappears. This is an obstruction to that proof route, not to polarization universality.

A slit/horseshoe version would need an alternative event that preserves the distinguished arm, produces a canonical residual boundary class, and couples its conditional Radon–Nikodym weights. The source's attached-wall estimate controls paths avoiding W walls under the prior law; it does not compare the arm-conditioned residual kernels. No such alternative kernel or contraction has been proved here.

## Exact finite warning: current support does not inherit the comparison order

Consider the square-lattice graph made of two adjacent unit squares. It has six vertices and seven edges. Condition the five-edge spanning tree (the shared vertical edge and all four horizontal edges) to be current-open. The only undecided edges are the two outer vertical edges L and R. The support weight from the source is

    w(N)=2^{k(N)} sum_{O subset N, O Eulerian} y^(|N|-|O|),
    y=c-1 in (0,1].

All four conditioned supports are connected, so k=1. Their exact unnormalized weights are

    w00=2y^5,
    w10=w01=2(y^6+y²),
    w11=2(y^7+2y³+y).

The empty odd set always contributes. Each individual square contributes a four-edge Eulerian set, and when both edges are present the outer six-edge perimeter is the remaining nonempty Eulerian set. Thus

    w11*w00-w10*w01 = 4y^4(y²-1).                              (7)

For EVERY y in(0,1), this is negative. After dividing by the square of the total weight, it is exactly Cov(1_L,1_R) under the stated conditioning. Hence conditional positive association of the N-edge indicators fails throughout the interior critical line. At y=1 the determinant is zero, as required by the FK(4) endpoint. This does not contradict source comparison: that proposition concerns the enlarged spin/percolation order, not the current-edge order. Nor does it prove that no conditioned-arm coupling exists. It excludes importing the ordinary conditional-FKG random-cluster coupling without a new argument.

## Why smooth Gaussian convergence alone does not identify lattice signs

Here is a logical diagnostic, outside the AT model. Given any integer-valued lattice heights H_delta, add independent variables epsilon_v with probabilities P(0)=1/2 and P(1)=P(-1)=1/4. For a compact smooth test phi,

    Var(delta² sum_v epsilon_v phi(v)) = (delta^4/2) sum_v phi(v)² = O(delta²).

Thus this bounded perturbation vanishes as a distribution on every fixed test and preserves any existing joint Gaussian limit of smooth height tests; bounded perturbations also preserve fixed-order logarithmic moment upper bounds after adjusting constants. But (-1)^(H_delta(v)+epsilon_v)=(-1)^H_delta(v) zeta_v, where zeta_v are independent fair signs. Every off-diagonal spin correlation is erased. For any proposed normalization b_delta with delta/b_delta->0, the normalized perturbed spin test has variance O(delta²/b_delta²)->0 rather than nonzero imaginary chaos.

These modified heights violate the exact six-vertex increment/edge constraints and are NOT competing AT configurations. The example only demonstrates that the smooth-field topology and logarithmic moment bounds cannot justify applying the oscillatory nonlinear map. The model-specific constraint is precisely where the unpaid microscopic argument must enter.

## Current outcome

The full unchanged target is unresolved. No all-coupling ratio limit, collision majorant, or surviving-arm regeneration has been proved. The source and primary comparisons identify the precise missing operation, and(7) rules out a tempting false monotonicity shortcut. Neither the finite diagnostic nor the absence of a located theorem supplies contribution value. A continuation should work on the decorated conditioned-arm kernel or an equally strong microscopic charge estimate, not repeat Gaussian convergence, the paid excursion transfer, or an Ising-only specialization.
