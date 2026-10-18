# Temporal scalar integrability: a pre-freeze screen

Myeongjin Kang; no affiliation. Original prose CC BY 4.0; original code MIT. Pinned source truths are premises. This is author research, not an independent review.

## Question and chronology

The prospective question is: does every smooth Ricci flow on every closed connected smooth four-manifold M, with smooth initial metric, on a finite interval [0,T), extend smoothly on the same M past T if

    integral_0^T S(t) dt < infinity,    S(t)=max_M |R(g(t))|?

No Ricci lower bound, Type I bound, spatial scalar Lp hypothesis, topological restriction or restriction on degeneration is proposed. This question is NOT frozen as a candidate theorem: the actual-source/primary feasibility screen has not produced a complete mechanism. It remains unproved and unrefuted here. It is distinct in hypotheses from I27's already developed spatial-Lp continuation question, but it encounters some of the same source interfaces; this does not constitute novelty clearance.

The bounded-scalar source351 extends smoothly under sup S<infinity. Its static input is E=o(M) on a fixed finite Ricci-flat tree. The precise geometric hypotheses cannot be discarded. Hamanaka2104.10300v3 Main Theorem1 requires BOTH temporal integrability and a fixed-radius small local spatial Lp0 scalar bound, p0>2, and concludes orbifold convergence/continuation. Its Lemma2.5 uses spatial critical-norm absorption for noncollapse; Lemma2.7 invokes the stronger spatial norm for Ricci improvement. He2014's integral-Ricci criterion is only read as quoted in Hamanaka, not its original body. It cannot be applied to scalar integrability alone. No primary cited here supplies the proposed full conclusion.

## A conditional local estimate that really follows

Let a smooth four-dimensional Ricci flow have an already controlled parabolic coordinate cylinder of radius ell and time length comparable to ell^2. Assume its rescaling to a fixed unit cylinder has uniformly elliptic metric, bounded coefficients and the finite spatial derivatives needed below, volume density uniformly comparable to Euclidean, and |Rm|<=C ell^-2. Reserve fixed smaller cylinders for cutoffs, integration and evaluation. These are CONDITIONAL cylinder assumptions, not consequences asserted from temporal scalar integrability.

Let eta=integral_J S(t)dt on the time interval of the larger cylinder. A nonnegative compactly supported spacetime cutoff psi, equal to one on an intermediate cylinder, has |partial_t psi|+|Delta psi|<=C ell^-2. Use d/dt dmu=-R dmu and (partial_t-Delta)R=2|Ric|^2. Integration by parts, with no temporal boundary term, gives

    2 integral psi |Ric|^2
      = integral [-R partial_t psi - R Delta psi + R^2 psi].                 (1)

Here and below the integrals in (1) are spacetime integrals with the evolving volume. On the support, |R|<=C ell^-2 from the assumed curvature bound, so R^2<=C ell^-2 |R|. Its spatial volume is at most C ell^4. Consequently

    integral_intermediate |Ric|^2 <= C ell^2 eta.                            (2)

The Ricci equation is homogeneous linear in Ricci after fixing the controlled curvature coefficients. Interior L2-to-sup parabolic smoothing, on the reserved smaller cylinder, therefore gives

    |nabla^k Ric| <= C_k sqrt(eta) ell^(-2-k).                               (3)

For k=0 the scaling factor from the spacetime L2 norm to supremum is ell^-3 in dimension4, and (2) supplies ell sqrt(eta). For higher k use the assumed coefficient derivative bounds and interior differentiated estimates. This is exactly the kind of fixed-cylinder operation used in source351 geometry.tex306–355 and parabolic.tex's local-smoothing framework. Equation (3) is not a new global regularity theorem.

For an integrable S, eta tends to zero uniformly for windows contained in a sufficiently late time tail. Thus already controlled small-scale limits are Ricci-flat. This recovers a useful qualitative input. It does NOT provide those cylinders, a uniform L2 curvature-energy bound, all-ball noncollapse, a uniformly finite bubble tree, the source's neck decay, or control of material collars.

Compare the bounded-scalar source: eta<=C ell^2 produces |Ric|<=C ell^-1. In its buffered interval units this is C epsilon/r, not merely sqrt(eta)/r^2. The source's geometric-motion and cutoff-forcing estimates explicitly use this extra power of radius (parabolic.tex, para:source-scale). A time-tail modulus without a relation to each spatial scale cannot be substituted with the same constants.

## The scalar-square loss is not bounded by temporal L1 bookkeeping

On a buffered interval of fixed normalized length, with root length a, source351 final:variation retains a true core of volume O((Na)^4). Its first variation there is

    <(R/2)g-Ric,-2Ric> = 2|Ric|^2-R^2.

For bounded original scalar, the normalized scalar is O(epsilon_i^2); the scalar-square loss is O(epsilon_i^4 N^4 a^4)=o(a^4). Temporal integrability instead gives only a small L1 norm of the normalized scalar supremum. Indeed parabolic normalization by original time length d changes R to d R and dt to dt/d, preserving this L1 integral. The direct upper bound for the normalized loss is

    a^-4 integral_core R^2 <= C N^4 integral_I S_i(t)^2 dt,                 (4)

and the right side does not follow to zero from integral S_i ->0.

An exact scalar diagnostic illustrates the missing inference even with natural curvature-scale time derivative bounds. Fix nonzero phi in Cc-infinity((0,1)), phi>=0, and a->0. Put

    S_a(t)=a^(-3/2) phi((t-t0)/a^2).

Its support lies in one fixed interval for small a. Then

    integral S_a = a^(1/2) integral phi ->0,
    integral S_a^2 = a^(-1) integral phi^2 ->infinity,
    ||partial_t^k S_a||infinity = a^(-3/2-2k)||phi^(k)||infinity
                              <= C_k a^(-2-2k),   0<a<=1.

In particular adding the crude scale bounds S<=C a^-2 and |S'|<=C a^-4 does not repair (4). These functions are NOT Ricci flows or a counterexample to continuation. The point is only that the proposed estimates do not imply the required scalar-square conclusion.

This phenomenon can also coexist with the direction of the scalar maximum-principle inequality. On Euclidean R4, put

    v_a(x,t)=a^(-3/2)(1+t/a^2)^(-2) exp[-|x|^2/(4(a^2+t))],   t>=0,
    J_a(t)=integral_0^t ||v_a(s)||infinity ds,
    R_a(x,t)=v_a(x,t)/(1-J_a(t)/2).

For small a, J_a(infinity)=sqrt(a)<1, and v_a solves the Euclidean heat equation. Direct differentiation gives

    (partial_t-Delta)R_a = (1/2)||R_a(t)||infinity R_a >= (1/2)R_a^2.

Moreover integral_0^infinity ||R_a||infinity dt = -2 log(1-sqrt(a)/2)->0, while integral_0^1 ||R_a||infinity^2dt >= c/a. Thus positivity of the scalar reaction alone, without the coupled metric/Ricci system, does not eliminate the concentration. This remains a scalar PDE diagnostic on Euclidean space, NOT a geometric construction and NOT an upstream objection.

## Two possible repairs tested, neither completed

1. **Time-dependent uniform rescaling/integrating factor.** Let c(t)>0 have log c controlled by integral S. On a closed manifold the unrenormalized Einstein–Hilbert integral has E'=2 integral |Ric|^2-integral R^2. A scaling changes its derivative by a multiple of S E. But source351 uses the renormalized E=integral R minus an asymptotic flux; the two terms need not converge separately (static-input.tex). There is no supplied inequality integral_core R^2 <= C S E, and E need not be positive. Replacing it by an unrenormalized integral loses the static o(M) conclusion and introduces the uncontrolled flux. Uniform scaling also leaves unbounded S unbounded when its factor stays bounded above/below. No integrating-factor proof is obtained.

2. **Absorbing the trace by a scalar energy estimate.** Formally testing the scalar equation by a cutoff times R could control gradient energy using a small curvature-scale scalar bound. A Poincare estimate might then make the R^2 term small relative to Ricci energy. But the actual core contains arbitrarily smaller descendants; no uniform Poincare/trace estimate with the needed boundary terms and root normalization has been proved from temporal integrability. Even such an estimate would not by itself supply the missing finite-tree/energy compactness. This is a possible route, not a lemma, theorem or conditional nominee.

## Disposition

Pre-freeze NO NOMINEE. Conditional (1)–(3) and the exact scalar diagnostics clarify the interface; they do not settle the full temporal-only question. No spatial-Lp assumption, uniform tree bound, or added curvature hypothesis is adopted to make an easier theorem. No claim that source351 or Hamanaka exhaust all possible methods. No substantiality or independent-proof gate is claimed; zero count.
