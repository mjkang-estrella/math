# r150 — central potentials and intrinsic volume

Research derivations; PREFREEZE/no nominee. All Source051 operations at the pin are stipulated. No author proof of a frozen theorem or mathematical grade is offered. The question under investigation is the full compact smooth hyperbolic class, with no pinching or shape assumption.

## 1. The actual paid source chain

The source convention is dd^c=i∂∂bar, R_h=−dd^c log det h, [−R_h]=2πc1(K_X), and h^n has no 1/n! factor. Hyperbolicity means absence of actual nonconstant entire maps, and compact Brody rescaling gives a background squared central derivative bound D. It does not assert smoothness or convexity of the infinitesimal metric.

For d(f)+P_q(f)−δA_h(f), the negative outer-annulus density gives existence by normality, Fatou and interior derivative convergence. Dilation gives an area tail bounded by C_f(1−r). The resulting continuous W^{1,p} regularity, 2<p<4, is individual to the maximizer. Weighted Hardy factorization, its rotation-difference estimate, and the centered nonlinear Cauchy right inverse then produce actual families with ∂_{t_j}F(0,z)=zb_j(z). They are holomorphic into W^{1,p0}, p0>2, and boundary-unitary for h. In particular, merely writing down an infinitesimal section is not the source operation.

Writing N=B*hB, the source proves

    log det N(0)=P_{R_h}(f),
    L P_q(F)=mean_boundary tr_h q,
    L A_h(F)=n−A_{R_h}(f).

The last identity uses a sequence of radii where the radial trace-minus-logdet error vanishes. No extension past the circle is presumed. The sign of the determinant identity is important.

The Ricci-disc upper bound yields a bounded positive canonical weight via the determinant-line Poletsky envelope. Smoothing compares sup regularizations at fixed radius ratios with error O(1/|log r|), then uses an exact-deletion regularized maximum. It gives near positivity without asserting uniform convergence of the original bounded weights. The negative-sign Monge–Ampère equation provides h_t with R_{h_t}=−h_t+tk. Positive canonical volume is obtained by a cohomology polynomial, not convergence of h_t. Big plus no rational curves, after projectivity, gives ampleness. These are all already paid.

Canonical ampleness also permits the ordinary negative Kähler–Einstein solution h with R_h=−h. Its use below does not add a new projectivity or existence theorem. In fact all central-potential estimates below hold for any smooth Kähler h with R_h≥−h.

## 2. Replace the central quadratic term without changing the boundary argument

Fix x and linear holomorphic coordinates on T_xX. Let V_x be the closure of all derivatives f'(0) of discs with f(0)=x. Source normality makes V_x compact. It contains a neighborhood of zero by local coordinate discs and is balanced by source rotations and dilations. Finite-area discs are dense for central derivatives: f(rz) extends past the unit circle and r f'(0)→f'(0). The open raw indicatrix I_x={v:κ_X(x;v)<1} has closure V_x; this follows directly from the infimum definition and dilating discs. No tangent metric regularity is needed.

Let ψ be a smooth real function on a neighborhood of V_x, with ψ(0)=0 and ψ≤D on V_x, D>0. Assume its complex Hessian Lψ is positive definite there. Take a,b>0 and maximize

    J(f)=ψ(f'(0))−a P_h(f)−b A_h(f),       f(0)=x.       (2.1)

All discs in (2.1) have finite area. This is not a formal substitution into a theorem whose central term is fixed; here are the interfaces:

• ψ is bounded on the compact derivative set. The source negative-tail proof, now with q=−a h and δ=b, bounds area on a maximizing sequence. Interior convergence gives convergence of ψ(f'(0)). Hence the same Fatou argument gives an actual maximizing disc.
• Dilation compares (2.1) with f_r. If v=f'(0), maximality implies

    0≤b(A_h−A_{h,r})
      ≤ψ(v)−ψ(rv)−2a∫_r^1 A_{h,s} ds/s
      ≤Cψ(1−r).                                      (2.2)

The last estimate uses a bound for the real derivative of ψ on the compact radial set {rv}. Positivity of A_h allows dropping the integral. The source background metric still provides normality and chart control; ψ need not be a metric on X. Thus the exact source boundary-regularity proof applies, with constants depending on ψ,a,b,h,x.
• Source frames and sprays apply to this individual boundary-regular disc. Since F(t,0)=x, v(t)=∂_zF(t,0) is a holomorphic map to the fixed vector space T_xX and ∂_{t_j}v(0)=b_j(0). Therefore

    L ψ(v(t))=tr(B(0)* Lψ(v) B(0)).                    (2.3)

There is no mixed acceleration term: v(t) is holomorphic. This also explains why replacing ψ by a nonsmooth intrinsic norm without regularization would be unjustified.

The constant disc has J=0, so with P=P_h(f), A=A_h(f),

    aP+bA≤ψ(v)≤D,             P,A≥0.                 (2.4)

With R_h≥−h, the Hessian maximum and determinant identities imply

    tr(B* Lψ(v) B)≤n(a+b)+bA,
    det(B*hB)=exp(P_{R_h}(f))≥exp(−P).               (2.5)

Everything so far is for a,b>0 separately. There is no uniform variation radius or W^{1,p} norm as b tends to zero.

## 3. Use the JOINT energy budget before passing to the limit

Put s=bA∈[0,D]. By (2.4), P≤(D−s)/a. The determinant quotient and AM–GM give

    det h(x) ≥ exp(−(D−s)/a)
                [n/(n(a+b)+s)]^n det Lψ(v).         (3.1)

The logarithmic derivative of the scalar factor in s is

    1/a−n/[n(a+b)+s] > 0.

Thus its minimum is at s=0, rather than at two incompatible separate worst cases for P and A. If mψ=inf_{v∈V_x}det Lψ(v)>0, we obtain

    det h(x)≥exp(−D/a)(a+b)^(−n) mψ.

For each b>0 the conclusion is about the SAME det h(x) and mψ. Taking the supremum as b↓0 is an ordinary scalar limit, not a limit of discs or frames. Optimizing a gives a=D/n and

    det h(x) ≥ (n/(eD))^n mψ.                       (3.2)

This uses the full source mechanism but remains a research reduction. The parameter optimization alone is not offered as a nominee.

## 4. Entirely pay the Hermitian and convex-hull reductions

For any positive Hermitian matrix Q with v*Qv≤1 on V_x, use ψ(v)=v*Qv, D=1. Then

    det h(x)≥(n/e)^n det Q.                         (4.1)

The optimization is over all tangent-space forms Q. No globally Kähler extension of Q with a controlled Brody bound is required. Let E_x be the minimal-volume centered complex ellipsoid containing V_x and Q_x its matrix. Existence and uniqueness follow from the standard minimal-ellipsoid construction; boundedness and an interior ball prevent degeneracy of the maximization of log det Q. The constraints only see conv(V_x), since the ellipsoid is convex. Thus (4.1) reaches precisely the unnormalized Wu ellipsoid, not the raw indicatrix volume.

If ω_{2n}=π^n/n! is the Euclidean complex unit-ball volume, then Vol(E_x)=ω_{2n}/det Q_x. Complex John containment gives

    conv(I_x) ⊂ E_x ⊂ sqrt(n) conv(I_x).

Here is the finite-dimensional contact argument, to keep the classical bridge explicit. Transform the optimal ellipsoid to the Euclidean unit ball. Its contact vectors u have norm one. Optimality forces I into the positive cone generated by uu*: otherwise a separating Hermitian H has tr H>0 and u*Hu≤0 on all contacts. Replace H by H−ηI for sufficiently small η>0. This retains positive trace and makes all contact inequalities strict. Compactness then makes I+τ(H−ηI) feasible for all sufficiently small τ>0, while its determinant increases, a contradiction. The contact cone is closed because each generator has trace one; a bounded trace bounds the total coefficient mass. Finite-dimensional conic reduction gives I=Σc_j u_j u_j*, c_j≥0 and Σc_j=n. For ||z||≤1,

    z=Σc_j (u_j*z)u_j,
    Σc_j |u_j*z|≤sqrt(Σc_j) sqrt(Σc_j |u_j*z|²)
                    =sqrt(n)||z||≤sqrt(n).

Balance and convexity now place z/sqrt(n) in the convex hull. This proves the stated containing-ellipsoid inclusion, with its direction and constant. It is the classical contact-decomposition operation, not a new contribution claim.

Consequently (4.1) implies the explicit convexified comparison

    det h(x) Vol(conv(I_x)) ≥ e^(−n) ω_{2n}.         (4.2)

This is coordinate invariant: the determinant and tangent volume change by reciprocal squared complex Jacobians. It is a consequence of source Hessians plus the classical minimal ellipsoid, not a claimed substantial theorem. Replacing conv(I_x) by I_x strengthens (4.2), since Vol(I_x)≤Vol(conv(I_x)); that implication has the WRONG direction and cannot be silently used.

The actual Chakrabarti–Mahajan complex Binet–Legendre construction uses the covariance of the convexified unit ball, then dualizes. Its regularity, product and covering operations have been read, not inferred from its abstract. Those operations pay another Hermitian representation of the same convexified data. They do not restore the discarded nonconvex volume. In their v1 §3.3, the displayed Wu norm comparison has the inclusions' direction reversed for their stated minimal-CONTAINING-ellipsoid definition. Here the normalization is fixed by E_x={v:v*Q_xv<1}, so the correct inequalities are κhat/sqrt(n)≤sqrt(Q_x)≤κhat. Our derivation uses the inclusions directly and does not import that displayed comparison.

Nikolov–Pflug's actual Proposition3 and proof close convexification by 2n−1 tangent summands (with a sharp example); the theorem expressly extends to manifolds. Summands are not one holomorphic disc. It therefore supplies neither a raw-volume comparison nor a smooth family realizing every convex combination by a single disc.

## 5. A nonconvex diagnostic that is itself an actual domain indicatrix

For n≥2 and 0<p≤2 set

    Ω_p={z∈C^n: Σ|z_j|^p<1},       t=2/p≥1.

This is a bounded balanced pseudoconvex domain: log(Σ|z_j|^p) is plurisubharmonic, as can be seen by regularization or the log-sum-exp rule. Its Minkowski functional is μ_p(z)=(Σ|z_j|^p)^(1/p). It is the actual Kobayashi–Royden norm at zero of Ω_p, not an arbitrary star body. Indeed for f:Δ→Ω_p, f(0)=0, the function log μ_p(f(z)/z), extended at zero, is subharmonic. On |z|=r it is ≤−log r. The submean principle and r↑1 give μ_p(f'(0))≤1. Conversely z↦zv/μ_p(v) realizes equality. This is the balanced pseudoconvex operation used in the actual Nikolov–Pflug example.

For p<1, Ω_p is not convex. Its convex hull is exactly the complex ℓ¹ ball {Σ|z_j|<1}: Ω_p is contained in that ball and contains every coordinate unit disc, whose convex hull is that ball. The ellipsoid containing Ω_p has Q=I. To see the latter without an unproved optimization, each coordinate unit vector forces Q_jj≤1, and Hadamard gives det Q≤∏Q_jj≤1. The Euclidean unit ball contains Ω_p, so equality is attained.

Polar coordinates and the Dirichlet integral give

    Vol(Ω_p)=π^n Γ(1+t)^n / Γ(1+nt).                 (5.1)

For completeness, put y_j=|z_j|^p. Then planar area is (2π/p)y_j^(2/p−1)dy_j, and integrate ∏y_j^(t−1) on Σy_j<1. This yields (5.1). For n≥2 the volume tends to zero as p↓0, while the convex hull and enclosing ellipsoid stay fixed. Therefore no arbitrary-balanced-pseudoconvex-body volume comparison can repair (4.2).

This is NOT a compact hyperbolic Kähler counterexample. No construction realizes these indicatrices in that compact class, and no Ricci-normalized metric on Ω_p is asserted to violate the full prospective question. Its use is limited to diagnosing what shape information Hermitian tests discard.

## 6. Nonlinear central potentials: exact smooth Levi calculation

The natural next test retains the raw shape:

    ψ_ε(z)=[Σ(|z_j|²+ε²)^(1/t)]^t − n^t ε²,       ε>0.       (6.1)

This is globally smooth, ψ_ε(0)=0, and strictly plurisubharmonic. It approximates μ_p² but is legitimate at every coordinate axis and at the origin. Put

    a=1/t=p/2, u_j=|z_j|²+ε², S=Σu_j^a,
    w_j=u_j^a/S, σ_j=ε²/u_j,
    d_j=a+(1−a)σ_j ∈[a,1].

A direct differentiation gives a positive diagonal part plus a positive rank-one part:

    Lψ_ε = S^(t−1) diag(u_j^(a−1)d_j)
            +(1−a)S^(t−2) vv*,
    v_j=u_j^(a−1) conjugate(z_j),

with the usual matching choice of column convention. The determinant is independent of transposing that Hermitian representation. The determinant lemma gives exactly

    det Lψ_ε
      = S^[n(t−1)] ∏u_j^(a−1)
          [Σ_i w_i ∏_{j≠i}d_j].                  (6.2)

Indeed the rank-one factor is

    1+Σ_i w_i(1−d_i)/d_i = Σ_i w_i/d_i.

Hence the bracket is at least a^(n−1). Also ∏u_j^a≤(S/n)^n, so because a−1≤0,

    det Lψ_ε ≥ t^(−(n−1)) n^[n(t−1)] =: L_{n,t}.  (6.3)

This is GLOBAL and UNIFORM in ε. It proves the exact missing smooth-axis interface; no nonsmooth Hessian is substituted at a maximizing derivative.

For z∈closure(Ω_p), concavity gives S≤1+nε^p, so

    0≤ψ_ε(z)≤(1+nε^p)^t−n^tε²=:D_ε,    D_ε→1.   (6.4)

If the central derivative body at the point under study is linearly identified with closure(Ω_p), equations (3.2), (6.3), (6.4), then ε↓0, give

    det h(x) ≥ (n/e)^n L_{n,t}.                   (6.5)

More generally this is a valid central-test calculation on any derivative body contained in that domain after the same linear change. It is a method computation, not a separate restricted theorem nominee.

At a nonzero vector with all |z_j| equal, ε↓0 gives equality in (6.3). Thus the factor cannot be improved for this particular smooth-limit potential merely by estimating its determinant more carefully.

## 7. Optimize the entire sum-radial class, not only one trial power

Away from coordinate axes let s=Σ|z_j|^p and consider ψ(z)=f(s), with f(0)=0, f(1)=1, f'>0 and f'+s f''>0. Its Levi determinant is

    det Lψ = (p²/4)^n f'(s)^(n−1)[f'(s)+s f''(s)]
                              ∏|z_j|^(p−2).       (7.1)

For fixed s, the product is minimized at equal moduli, because p−2≤0. Therefore a global determinant lower bound m in this class must satisfy

    f'(s)^(n−1)[f'(s)+s f''(s)]
       ≥ M s^[n(t−1)],
    M=m t^(2n) n^[−n(t−1)].                       (7.2)

Put y(s)=sf'(s). Then

    (y^n)' = n s^(n−1) f'^(n−1)(f'+sf'')
             ≥ nM s^(nt−1).

The limit y(0)=0 holds for a bounded monotone f with the indicated convexity in log s; otherwise integrating f'=y/s would make f unbounded. Integrating gives

    y(s)^n ≥ (M/t)s^(nt),
    f'(s) ≥ (M/t)^(1/n) s^(t−1).

Integrating again from zero to one and using f(1)−f(0)=1 yields M≤t^(n+1). Thus

    m≤ t^(−(n−1)) n^[n(t−1)] = L_{n,t}.           (7.3)

Equality is attained by f(s)=s^t, whose nonsmooth-axis issue is paid by (6.1)–(6.4). This is an exact optimality statement for the stated central-potential ansatz. It is not a bound on all plurisubharmonic central functions or on all source-based arguments.

Combining (5.1) with (7.3), Stirling gives

    L_{n,t} Vol(Ω_p)
      ~ π^n (2π)^((n−1)/2) n^(−n−1/2) t^(−(n−1)/2),
                                                       t→∞.       (7.4)

The exponentially small volume is largely recovered by the nonlinear Hessian: this is much stronger than the enclosing ellipsoid's fixed determinant. But a polynomial loss remains for every n≥2, and the ODE proves that changing the radial scalar profile cannot remove it within this class. For n=1 the expression equals π, consistent with the disc normalization; that case is not the outstanding higher-dimensional interface.

## 8. The exact general bridge, and what the primary constructions do pay

For a compact balanced derivative body V define, in the chosen tangent coordinates,

    C(V)=sup_ψ [inf_V det Lψ]/[sup_V ψ]^n,

where ψ is smooth on a neighborhood of V, ψ(0)=0, sup_Vψ>0, and Lψ>0 there. No differentiability of the Kobayashi norm is imposed. Equation (3.2) gives the complete reduction

    det h(x) ≥ (n/e)^n C(V_x).                     (8.1)

A dimension-only bound C(V_x) Vol(I_x)≥c_n>0 FOR THE ACTUAL COMPACT MANIFOLD DERIVATIVE BODIES would suffice for the desired raw-volume inequality. An alternative could exploit further relations between a maximizing derivative and its frame; (8.1) currently takes an infimum and deliberately discards those relations. Neither route has closed.

The two strongest fully implemented constructions are: (i) all tangent Hermitian tests, optimized by the actual minimal ellipsoid and complex John containment; and (ii) a smooth nonlinear central potential, its exact Levi determinant, and an ODE optimizing its whole radial class on a nonconvex domain model. The first loses raw shape; the second recovers its exponential scale but not a uniform normalized volume factor. These facts do not show C(V) Vol(I) tends to zero for the model, because the supremum in C(V) allows non-radial functions. Torus and permutation averaging may preserve lower determinant bounds by concavity of det^(1/n), but it only gives toric symmetric functions, not functions of Σ|z_j|^p. No unjustified reduction of that larger class is made.

The published Wu–Yau 2016 Proposition8 already supplies the twisted Monge–Ampère construction and cohomological limit; Proposition9 gives a tensor trace inequality using negative holomorphic sectional curvature. The published 2020 paper §4 pays the actual holomorphic-chart bound for κ by mapping small Euclidean discs through a nonsingular chart, and combines it with the Schwarz lower bound. Its §6 pays the continuity method, trace and determinant estimates, then uniform ellipticity and higher derivatives under the curvature/quasi-bounded-geometry hypotheses. These are stronger reductions than merely citing a metric-comparison title. The source hypothesis here gives neither those uniform charts nor their pinching constants. Canonical R_h=−h by itself cannot be substituted for negative HOLomorphic sectional curvature in that argument.

The optional Source051 consequences depend on separate Fujita and semialgebraic-cover manuscripts. They are not dependencies of (2.1)–(8.1), and their bodies are not imported or developed into another family. Their paid pluricanonical freeness and finite-cover conclusions are not nominees. The eligible original r25 frozen conjunction and its actual weighted-product/no-common-zero construction were read: it concerns a fixed NONCOMPACT pinched threefold and a bounded higher-codimension embedding, expressly not a uniform invariant-metric comparison. Its full target is preserved. Other old compact/relative/log/singular and uniform scopes supplied in the brief stay immutable; coarse lexical history omissions are not clearance for retrying them.

No theorem is frozen. The raw-volume operation remains unpaid at the specific shape-sensitive determinant interface above. The convexified bound, the nonlinear test and the radial optimum are retained research payments, not weaker substitute nominees, grades, an exhaustion claim, or a global impossibility claim.
