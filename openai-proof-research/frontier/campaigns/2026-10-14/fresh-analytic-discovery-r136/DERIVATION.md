# Forward smoothing after the source Calabi singularity — PREFREEZE

This is original working mathematics, not a frozen theorem or acceptance nominee. Source truth and its operative lower proofs are stipulated. The old r31 nonsymmetric stability question and I130/I133 fixed-metric harmonic question remain unchanged and are not proposed here.

## Full research question

Does at least one of the U(10)-invariant initial metrics constructed by Source352 have a canonical weak Calabi trajectory on CP^10 which is represented by smooth positive Kähler metrics at every time in (T_*,T_*+epsilon), for some epsilon>0, after its first finite smooth singular time T_*? The class stays [omega_FS], the underlying complex manifold stays CP^10, and the continuation is the E^2 Mabuchi-gradient-flow trajectory from the SAME initial metric. Existence of an unrelated expander, a radial formal solution, a subsequential weak limit, or smoothness away from the singular point does not answer this question. No nonsymmetric perturbation basin or codimension claim is made.

## What the integrated reduction already supplies

Source352 geometry: v=x(1-x)+x^2(1-x)^2H; b=1+x(1-x)H>0; S=110-K(H), K=x^-9 (x^11(1-x)^2H)''. The exact equation is H_t+b^2 A H=0, A=K''. Its compact construction gives H=F+V for t<0, F=(G(x/sqrt(-t))-1)/x, and V=O((x+sqrt(-t))^-1+delta), with scaled spatial derivatives and time regularity. On fixed positive x the coefficients and solution extend to t=0 through local estimates. At zero H~G'(0)/sqrt(-t).

The flat inverse is a future-forcing/past-forcing spectral split; its initial values are free. The compact proof cancels an inner cutoff commutator using the outer forward source and inverts the remaining small mismatch. Both are operative inputs, not new operations.

Berman–Darvas–Lu's EVI theory already gives a unique global weak trajectory from the smooth initial potential, agreeing with the source trajectory before T_*. Its continuation and the existence of its d2 trace at T_* are therefore paid. EVI contraction also pays identification of ANY post-time smooth solution that tends to this trace in d2: compare it on [epsilon,t] to the weak trajectory and send epsilon down to zero. A new proof need not independently reconstruct a weak flow or its uniqueness.

## Momentum trace and fixed holomorphic coordinates

The source bound suggests, and its weighted spatial estimates give on the punctured trace,

    v_0(x) = c x + O(x^(1+delta)) + O(x^2),  x down to 0,

where c=(1+d)^-1 and d belongs to the source's narrow box around 0.400682721856639. Thus c is about 0.714, strictly between zero and one. Work at fixed x_0>0. The source affine normalization is u_t=K(H); away from zero K is bounded as t tends to zero, so u'(t,x_0) has a finite limit. Since u''=1/v,

    u_0'(x) = c^-1 log x + A + O(x^delta),
    q=|Z|^2 = e^A x^(1/c)(1+O(x^delta)),
    x = e^(-cA) q^c(1+O(q^(c delta))),
    Phi_0(q)-Phi_0(0) = e^(-cA) q^c/c + O(q^(c+c delta)).

Here replace delta by min(delta,1) if needed. These are punctured asymptotics with derivative control inherited from the source weighted estimates; no time-dependent affine gauge is silently discarded. The tangential and radial Hermitian eigenvalues are x/q and v/q. Both diverge like a positive constant times q^(c-1). The trace cannot be an L-infinity metric relative to any smooth positive background in a neighborhood of the point. Holomorphic coordinate changes with nonsingular derivative do not change this unboundedness.

The formal trace is bounded as a potential and hence belongs to every finite E^p. Its radial measure is proportional to x^9 dx; equivalently det(g)~constant*q^(10(c-1)), and Euclidean radial volume is q^9 dq. Entropy integrability reduces to integral_0^epsilon q^(10c-1)|log q|dq<infinity. Bounded potential is not a bounded metric. Trace matching in d2 can be approached by uniform convergence of normalized potentials (whose straight-line path bounds d2 by volume^(1/2) times the sup difference); the precise global limiting/extension argument should be written only if the forward construction closes.

He–Zeng's rough-data contraction operates near a smooth background in the L-infinity norm of the complex Hessian, so it cannot directly start from this trace. This is not the only reduction considered: one should combine its fourth-order local/outer estimates with the source weighted core gluing and EVI identification. What remains is a compatible positive forward core and its initial-trace inverse, not weak uniqueness.

## The forward core has the opposite profile equation

Let D=y*d/dy, Q(D)=(D-1)(D+9)(D+10), P(D)=(D-2)Q(D). The flat multiplier g satisfies

    g_t = -g^2 x^-2 P(x*d/dx)(g-1).

For t>0 put rho=sqrt(t), y=x/rho, g(t,x)=E(y). Then g_t=-DE/(2rho^2), so

    P(D)(E-1) = y^2 DE/(2E^2).

If E tends to the SAME c with the requisite differentiated tail, integrating the (D-2) factor fixes the integration constant and gives

    Q(D)(E-1) = -(y^2/2)(1/E-1/c).                 (E)

The source shrinker has the opposite sign. Taking E=G fails unless G is constant; reversing the time of a parabolic solution changes the PDE sign. This diagnoses only that shortcut, not nonexistence or novelty.

Write E=1+a y+b y^2+e y^3+... . The constant and linear terms leave a free. Since Q(2)=132 and Q(3)=312,

    b = (1/c-1)/264 > 0,    e = a/624.

For a conic tail E=c+A_1 y^-2+... the constant balance Q(0)(c-1)=-90(c-1) gives

    A_1 = 180 c^2(1-c) > 0.

The expanding tail approaches c from above. The shrinking coefficient has the opposite sign. These exact algebraic facts are diagnostics, not a full positive connection.

Use the source rescaling s=(27/16)^(1/3)(y/c)^(2/3), E=c(1+p), d=1/c-1. Equation (E) becomes

    p''' + (30/s)p'' + (751/(4s^2))p'
         - (1215/(4s^3))(p-d) - p/(1+p) = 0.      (E_s)

The limiting linearization is p'''-p=0, with roots 1 and -1/2 +/- i sqrt(3)/2. Its decaying subspace has real dimension TWO and growing subspace dimension ONE. The source shrinker has one decaying and two growing directions. At fixed c, the analytic origin family has one shooting parameter; a dimension count permits but does not prove a match to the two-dimensional tail manifold. Positivity 1+p>0 through the connection remains essential. The shrinking certificate provides no certified expanding connection.

## Next attempted operation and exact obligations

A full closure would require a global positive E for the actual source c, not a nearby adjustable cone, with a differentiated expansion; a forward weighted inverse preserving the t=0 singular trace; compact nonlinear correction with positive metric; and d2 convergence to the source trace. EVI then identifies the trajectory, paying the weak-flow clause without a separate new mechanism. The source commutator cancellation and standard parabolic estimates should be reused wherever compatible.

We do not yet know whether a validated scalar shooting connection suffices or whether a nontrivial forward resonance obstructs the initial-trace problem. The source ancient inverse does not by itself fix an incoming trace: its future-selected components can change it. This is an operator-domain compatibility issue. Merely counting tail dimensions, failing a direct time reversal, or finding numerical shots would not settle it.

## Source-compatible tail construction: this part is paid

The half-line method in Source352 `prof:tail` and `prof:weighted-remainder` adapts directly to (E_s), with its two stable roots instead of one. It is not reasonable to call the entire expanding ODE an unpaid new mechanism merely because the sign changed.

Here is a concrete bounded-tail construction. Set C=-1215/4, B=751/4, d in [.40068,.40069], A=-Cd (so 0<A<122), and p_a=A s^-3. For the expanding operator E_+(p)=p'''+30p''/s+Bp'/s^2+C(p-d)/s^3-p/(1+p),

    E_+(p_a) = s^-6[-567 A + A^2/(1+A s^-3)].

For s>=512 its modulus is <5*10^-12. Write L_0=partial_s^3-1. Its roots are 1 and lambda_+/-=-1/2 +/- i sqrt(3)/2. The Green formula uses forward integration for both complex roots and backward integration for the real root. Each projection denominator has modulus 3; consequently the uniform operator bound on the three jet entries is 5/3. Prescribe a conjugate pair of stable coordinates h,bar(h), |h|<=5*10^-7. The stable homogeneous jet H has sup norm <=10^-6.

Writing p=p_a+W, W=H+Kj, N(p)=p^2/(1+p), the source equation is

    j = -E_+(p_a) -30 W''/s - B W'/s^2 - C W/s^3
                         -N(p_a+W)+N(p_a).

On ||j||_infinity<=10^-7, ||W||_jet<=7*10^-6/6 and |p|<3*10^-6. Hence |N'|<7*10^-6. The coefficient sum is less than .060, giving contraction factor <.100. Its value on the ball is bounded by

    5*10^-12 + .060*(10^-6+(5/3)*10^-7) < 10^-7.

This proves a positive bounded two-parameter tail, continuously depending on d and h, by the same source operation. Iteration on functions tending to zero gives a vanishing tail. Replacing the constant norm by polynomial weighted norms on a sufficiently later half-line gives the differentiated expansion, by the source's bounded/weighted uniqueness argument, with the roots interchanged. This does NOT connect the tail to E(0)=1. Positivity here is only for the tail s>=512.

The origin recurrence also adapts. With r=s^(3/2), p=d+kr+sum_{i>=2} a_i r^i, the recurrence is

    a_i = -[r^(i-2)]((1+p)^-1-1)
                         /[(27/8)(i-1)(i+9)(i+10)].

For |k|<=.04, d in [.40068,.40069], in the radius-3 power-series algebra the ball sum_{i>=2}|a_i|3^i<=.1 has total nonconstant norm <=.22. The reciprocal norm is at most 1/1.18068<.848. Every denominator exceeds 440. The recurrence map has norm at most 9*(1+.848)/440<.038 and Lipschitz constant at most 9/(440*1.18068^2)<.015. Thus an analytic origin family exists and stays positive on this local interval. This local family and the far tail are standard contractions, not a full matching proof.

## Bounded numerical probe and its failure to certify matching

`expander_diagnostic.py` uses only Python's standard library. At the central d (NOT the unspecified exact source d), 40 origin coefficients at s=1 and RK4 with step .005 were used on s<=20. Eleven initial slopes in [-.4,0] were probed, with early stopping at p<=-.95 or p>=5. Forty-two bisections fitted an approximate unstable projection at s=20. The resulting k was about -.02228936304 and p(20) about .01473637. Halving the step gave a nearby finite value, but extending the same shot to s=30 gave p(30) about .20866645 and positive first/second derivatives. The endpoint condition retained only the first asymptotic term and did not select the exact stable tail. This is a useful sensitivity diagnostic; it is not a certified positive profile, not transversality, and not a basis for a scope freeze. No more parameter search was performed.

## The forward operator and why the original ancient inverse is insufficient

Conditional only for this calculation on an expanding E, let F(t,x)=(E(x/sqrt(t))-1)/x, A_f(zeta)=E(|zeta|^2)^2 and B_f(zeta)=y E'(y)/E(y), y=|zeta|^2. For V=rho^-1 v, rho=sqrt(t), tau=log t, zeta=z/sqrt(rho), the exact flat linearization becomes

    v_tau + A_f Delta^2 v/16 - (zeta.grad v)/4
                               +(-1/2+B_f)v = f#.

The signs of both dilation and constant term reverse relative to `flat:similarity-equation`; this is not the auxiliary-vs-physical angular issue of old r31. We stay inside the source invariant class.

At infinity its constant model semigroup on C_0(R^24) is

    S_c(s)d(zeta) = e^(s/2) (k_theta(s) * d)(e^(s/4)zeta),
    theta(s)=c^2*(e^s-1)/16,

where k_theta has Fourier multiplier exp(-theta|xi|^4). This identity follows by differentiating the dilation and the integrated heat time. Its norm is bounded above by C exp(s/2). Broad unit plateaus give the matching lower growth: at any fixed s choose a plateau much broader than the heat scale, so convolution tends to one at its center. For integer s=j this yields ||S_c(j)||>=exp(j/2). Thus the time-one spectral radius is exp(1/2).

The same growth is essential: choose disjoint broad plateaus escaping spatial infinity; they are weakly null in C_0, so every compact operator sends them to zero. Evaluate their time-j images at the corresponding dilated centers. The essential norm of S_c(j) is at least exp(j/2), while the upper bound gives essential spectral radius exp(1/2). This also works in the radial subspace using annular plateaus with both radius and width tending to infinity. It is a functional-analytic diagnostic, not a theorem about the nonexistent nonlinear continuation.

The source's shrinking model instead has essential radius exp(-1/2). Its choice of a circle between exp(-1/2) and 1 isolates finitely many complementary modes. Here a correction with delta in (0,1) scales as exp(delta*tau/2) near the core as tau tends to -infinity. The associated circle has radius exp(delta/2)<exp(1/2), inside the constant model essential spectral radius. The source's finite-dimensional Riesz argument therefore supplies no such split on the SAME C_0 space. This is not a proof that a forward inverse does not exist. Weighted trace spaces or a direct initial-value construction are compatible alternatives and must be tested.

A direct formulation retains the scalar auxiliary equation on R^24, with initial F_0=(c-1)/|z|^2. This datum lies locally in L^p for p<12 and weak L^12 at the scale-invariant exponent. Its principal multiplier 1+|z|^2 F_0 equals c off zero. A small-data perturbation about the biharmonic heat flow might construct a solution in a critical weighted space; however the actual c differs from one by about .286, and no quantitative contraction for this datum has been supplied. Shortening time does not reduce this scale-invariant deviation. We have not ruled out that stronger classical maximal-regularity or nonlinear monotone-operator methods pay this step. The full same-trace compact correction remains unresolved.

## Additional actual primary comparison

Huang, `1609.01834v1`, introduction plus modified blowup/smoothing proof: the smoothing theorem concerns invariant potentials on a flat complex TWO-torus. Its proof combines energy-compatible smooth approximations, weak-flow contraction, dimension-two curvature-energy control, a uniform curvature bound at positive times, and smooth compactness. That integrated approach is stronger than simply invoking weak existence. The missing analogue here is uniform positive-time curvature/metric control for approximations to the CP^10 cone trace. Finite entropy and bounded Mabuchi energy alone do not supply that control in the read theorem. Its unrestricted extension is not assumed. This comparison is bounded; no worldwide duplicate or priority assertion is made.

## Current disposition

PREFREEZE / no nominee. The full post-singular smoothing question above is retained, not replaced by the tail lemma, a finite-radius ODE shot, weak existence, or a smaller perturbation/cone scope. The actual unresolved operations are global positive matching at the exact source cone and a forward initial-trace construction (or an alternative approximation estimate giving uniform smoothness for every positive post-time). EVI identification, local/tail contractions and the source cutoff cancellation are credited operations. No correctness/contribution gate, independent review, formalization, manuscript, release or campaign count is assigned here.
