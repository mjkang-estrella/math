# I240 — independent contribution analysis

**Final classification: TECHNICAL. Do not accept as the tenth substantial finding.** This is an independent contribution judgment, conditional on mathematical correctness being settled by the separate proof gate. It is not a proof rejection, a claim that the exact theorem is already published, or a worldwide priority certification. I did not consult I239 or another live sibling. All pinned statements and lower operations are stipulated.

## 1. Exact object and burden of contribution

The authenticated submission is I236's complete analytic file, SHA256 `a30077ca36f40e6613e340d3f8ae0ac692000f7b39d6eb4113897f40b7c68931`. It was read in full, including the regularity lemma, cone infimum, nonlinear weak passage, harmonic replacement, slice alternatives and counterexamples.

For every integer m>=1, every finite tau>0 and every finite C0>=0, the theorem concerns V in C(R^m x R) solving

    G_tau[V] = V_tt + 2 DxV.DxV_t + DxxV[DxV,DxV] + tau Delta_x V = 0.

Upper C2 tests have G_tau>=0; lower tests have G_tau<=0. For every center (x,t) and every R>0, some p in R^m and a in R must satisfy

    |V(x+h,t+l)-V(x,t)-p.h-(a-|p|^2/2)l| <= C0 R
    whenever |l|<=R and |h-p l|<=R.                         (FIT)

The conclusion is affinity. There is no prior differentiability, global bound on either derivative, energy assumption or bound uniform as tau tends to zero or infinity. The naturally drifted version follows by a fixed shear and is the same finding, not a second one.

The local theorem actually established in the submitted argument is broader than SC_tau for one extremal pair: on any connected open Omega, a continuous spatially locally uniformly semiconcave G_tau-subsolution u below a continuous supersolution v cannot have an interior contact unless u=v. The intermediate theorem needs only u locally Lipschitz in all variables. This is the strongest ancillary formulation present. It should be recorded, but does not independently satisfy the substantial-discovery standard.

## 2. The parent's global-Lipschitz objection, resolved precisely

### 2.1 The classical case really is short

Suppose, additionally, that V is globally L-Lipschitz in all m+1 variables. Set

    a(p,q)=exp((q+|p|^2/2)/tau)(p,1),
    Da(p,q)=exp((q+|p|^2/2)/tau) A_tau(p)/tau,
    A_tau(p)[(xi,s)] = (p.xi+s)^2+tau|xi|^2.

The weak formulation is legitimate for a Lipschitz viscosity solution by the autonomous convolution/Fatou mechanism discussed below. On the full gradient ball |(p,q)|<=L, Da has fixed positive lower and finite upper bounds depending on L,tau. For any fixed translation h, the bounded function d_h(z)=V(z+h)-V(z) belongs to W1,2 locally and solves

    div(B_h(z) Dd_h)=0,
    B_h(z)=int_0^1 Da(DV(z)+s(DV(z+h)-DV(z))) ds.

This follows by subtracting the two weak equations, without differentiating V. B_h is measurable, symmetric and uniformly elliptic on the whole space, with the same constants at every radius. The scale-invariant oscillation decay from linear Harnack, iterated on expanding cubes, forces any bounded entire solution d_h to be constant. Thus V(z+h)-V(z)=c(h). Continuity makes c additive and linear, so V is affine. This supplies the exact bounded-gradient Liouville implication, not a slogan about pointwise ellipticity. The primary linear input is Crescimbeni–Forzani–Perini, Section 2 and Theorems 3.1–3.2; scale invariance and oscillation decay are explicitly stated there.

The global bounds on both p and q are sufficient here. A bound on p alone makes A_tau uniformly elliptic, but does not bound the exponential multiplier in Da because q occurs there. No undocumented q-bound or alternative nondivergence regularity argument is inserted.

### 2.2 FIT alone is genuinely weaker than a global gradient bound

The supplied I231 example can be checked independently. Set

    f(s)=s sqrt(log(e+s^2)),       V(x,t)=f(x1).

For center first coordinate x0 and radius R, choose T>|x0| with

    T=|x0|+(1+p)R,   p=sqrt(log(e+T^2))>=1.

Such T exists by the intermediate value theorem and sublinear growth of sqrt(log(e+T^2)). Take horizontal vector (p,0,...,0), ordinary time coefficient zero, and a=p^2/2. Every point of the required sheared box has |h1|<=(1+p)R=:D.

For |s|<=T,

    |f(s)-ps| <= (2|s|/p) log(T/|s|) <= 2T/(e p).

If |x0|<=2D, then T<=3D, and subtraction of the two affine errors bounds the fit residual by 4T/(e p)<=24R/e<9R. If |x0|>2D, the segment joining x0 and x0+h1 has |x0|/2<|s|<3|x0|/2. Writing q_s=sqrt(log(e+s^2)), one has p^2-q_s^2<=2log3, p/q_s<=sqrt(1+2log3), and

    |f'(s)-p| <= [2log3+sqrt(1+2log3)]/p <4/p.

Integration gives error at most 4D/p<=8R. Hence FIT holds with C0=10 at every center and radius, while f' is unbounded.

This is deliberately not a G_tau-solution: G_tau[V]=(f'^2+tau)f'' is not identically zero. It refutes FIT=>global Lipschitz, not PDE+FIT=>global Lipschitz. The latter implication would follow from the very affinity theorem being reviewed. One cannot demand a non-Lipschitz PDE+FIT example to prove strictness: that would contradict the candidate. The legitimate distinction is that the classical theorem requires an analytic hypothesis not supplied by the geometry, and no old result read here supplies it under FIT. Likewise the source growth O(R log^2 R) is not an O(R) bound, and the fit coefficients can accumulate logarithmically across scales. A local REG_tau estimate has not been established or silently invoked.

Consequently the correct negative verdict cannot be KNOWN merely because of the global-Lipschitz argument. I236 does bridge a real hypothesis gap. The contribution question is the nature of that bridge once the entire pinned envelope mechanism is free.

## 3. Subtracting the stipulated source content

The actual source was read, not inferred from its abstract. Section 03, thm:liouville, has exactly FIT but tau=0. Section 04 provides the frame change, dyadic fit comparison, logarithmic bounds, compactness with every fit quantifier and uniform subquadratic spatial tails. Those are equation-free apart from identifying the limiting PDE. The frame retains tau and finite-jet stability identifies G_tau; these are substitutions.

Section 05 already supplies the entire barycentric construction: quadratic penalty, least concave majorant, spatial semiconcavity, attainment, measure compactness, extremal Jensen quotient kappa, normalization, sandwich W<=V, and positive gap at contact. None of that is new contribution credit. The affine-slice preliminary case is replaced by a FIT midpoint identity, then source growth and the scalar equation c''=0; this is a useful elementary repair, not an independent rigidity mechanism.

For the viscous subsolution calculation, source 05's common-time theorem-of-sums direction is supplemented by the common horizontal translations E_k. The variance is invariant under each E_k, so the tau trace is precisely carried through. No new envelope, penalty, cancellation estimate or compactness theorem is required. This is the standard stability of the same envelope under an added common positive diffusion, correctly checked.

The candidate does NOT simply reuse sections 06–08. The homogeneous finite-Hamiltonian and discrete propagation arguments fail with the retained trace term, as I231 explains. I read source 08's actual final assembly: it gets a new limit with constant envelope slopes and invokes slope rigidity. I236 instead uses strong comparison on the contact pair and a zero-gap spatial maximizer. That is a real change of final mechanism. Its contribution has to be judged after granting the shared extremal construction, not by awarding novelty for constructing it again.

## 4. What remains, and why I classify it as technical

### 4.1 Spatial semiconcavity to time Lipschitz continuity

This is the best equation-specific observation. At (x0,t0), take a spatial supporting quadratic with bounded slope p and curvature K, then enlarge the curvature to K'=K+1. Continuity keeps the maximizers of

    h(t)=max_{|y-x0|<=r} [u(y,t)-p.(y-x0)-K'|y-x0|^2/2]

away from the boundary for a uniform short interval. An upper test psi for h lifts to an upper test for u with spatial Hessian K'I and zero mixed Hessian. Hence

    psi'' >= -K'[(|p|+K'r)^2+tau m].

The bounded scalar h is semiconvex, so its interior chord bounds give a Lipschitz estimate. Since h(t0)=u(x0,t0) and h>=u(x0,.), reversing the base times gives the two-sided bound.

This pays the time gap and is not contained literally in the pinned statement. It also avoids any false assertion of full space-time semiconcavity. But it uses a supporting quadratic, an interior maximum and the elementary one-dimensional characterization of convexity. Its constants may depend on the pre-existing compact time modulus; it produces no new quantitative modulus for the original fitted solution V. There is no novel regularization scale, iteration, coercive estimate on V or sharp exponent. The special property used is the coefficient 1 of psi'' and independence from u_t when the spatial Hessian is bounded. I assess this as an elementary structural lemma, not by itself a substantial discovery.

### 4.2 Exact contact through a cone infimum

For u locally L0-Lipschitz and L>L0, define locally

    v_L(z)=min_{|h|<=r} [v(z+h)+L|h|].

The inequality v(z+h)+L|h|>=u(z)+(L-L0)|h| keeps u<=v_L<=v, localizes minimizers near an old contact, and ensures that v_L=u forces h=0 and v=u. A fixed translate transfers lower tests because the equation is autonomous; using the same minimizing point proves the local L-Lipschitz bound. These facts hold for a broad class of autonomous, value-independent viscosity equations. The strict slope gap is a worthwhile detail and is needed, but it is exactly the elementary infimal-convolution comparison with a known Lipschitz obstacle. It does not introduce a new PDE comparison principle by itself.

### 4.3 The weak passage and linear comparison

Julin–Juutinen's primary Section 3 supplies precisely the non-singular autonomous sup/inf-convolution, Alexandrov Hessian, mollification and one-sided Fatou method; its introduction explicitly notes extension to other autonomous divergence equations. For the smooth exponential flux, already bounded full gradients make every coefficient bounded on a compact gradient ball, eliminate singular-gradient issues, and make the final nonlinear-flux limit a dominated-convergence argument. I236 appropriately writes this out rather than citing a p-Laplace statement as though it had the same operator. That diligence belongs to proof completeness. It is not an additional new regularity theorem.

The secant matrix int Da transforms the difference into a uniformly elliptic divergence supersolution. Linear Harnack/strong minimum is classical. The harmonic replacement with boundary trace is a correct way to use a reference stated for weak solutions; the same arbitrary-radius-sphere device appears in the older Ohnuma–Sakaguchi comparison architecture. No new Harnack estimate is proved or needed.

### 4.4 The combination

Together these arguments turn an already supplied semiconcave contact subsolution into a pair on which the standard monotone-divergence comparison machinery applies. The combination is useful and the initial obstacle is real, but the new global rigidity is carried by the stipulated extremal construction. The additional local steps are systematic localization and regularization, using an already known strictly monotone flux. There is no independent global estimate or new propagation phenomenon left after those inputs are granted. This is why I choose TECHNICAL rather than SUBSTANTIAL, while not pretending that the proof is the literally unchanged homogeneous proof or that its hypothesis gap never existed.

I applied the same distinction as the supplied I229 standard: a meaningful enlargement of the theorem's solution class does not automatically clear a prohibition on standard transfers from the full source proof package. The earlier negative verdict was not used as an authority about I236; I236's genuinely different contact route was assessed separately.

## 5. Primary comparisons and exact exclusions

1. Sánchez Morgado, arXiv:1712.10275v1, pp. 1–5: (EL), (4), (7) already give this exponential Euler–Lagrange equation with H=|p|^2/2 and k=1/tau. Lemma 1 assumes a C2 solution on the time-space torus and a structural bound on the lower-order term; Theorem 1 constructs smooth periodic solutions for the mechanical Hamiltonian. The proof uses the periodic global maximum of a two-point function. This is not an entire continuous FIT theorem. Its linearization is already symmetric uniformly elliptic once gradients are bounded.
2. Porretta, arXiv:2203.04856v1, pp. 1–13: (1.7) becomes G_tau after u=-V. Theorem 1.1 treats a bounded smooth convex spatial domain, positive W1,infinity marginal densities, Neumann spatial condition and specified temporal data. Theorem 1.2's whole-space statement has finite time, uniformly convex confining potential and Gaussian-comparable marginals. Theorem 3.4 requires a classical C3 interior/C2 closure solution of (3.4) and has constants depending on epsilon and W1,infinity data f^epsilon(mi), among other quantities. None removes the missing FIT-to-regularity step.
3. Peletier–Serrin (1978), printed pp. 66 and 68, actually read as page images: Theorem 1.1 assumes C3 entire solutions of Delta u=f(u,Du), bounded gradient and positive annular coercivity. Theorem 1.3 assumes bounded gradient, condition H and one-sided sublinear growth M(d)=o(d), as well as its displayed sign condition. Its stated extension to A(Du):D2u=0 still explicitly assumes bounded gradient and one-sided sublinear growth. These are not FIT, nor an affine Liouville theorem for its logarithmic-growth class. I do not invoke unseen later general theorems from that paper.
4. Trudinger (1988), first two PDF pages: F1 is uniform ellipticity and F2 requires a Hessian-independent Lipschitz constant in the gradient variable. G_tau fails F2 even on bounded p-balls as the Hessian varies. This does not license the missing direct viscosity difference inequality. I236's smooth solution-jet example makes that failure concrete. No broad application of Trudinger is made.
5. Ohnuma–Sakaguchi (2018), pp. 1–4: the warning about the earlier nonuniform gradient-dependent argument is explicit. Their Theorem 2.1 is for prescribed mean curvature and their method uses special classical Dirichlet replacements. It is not SC_tau, though the replacement-on-every-small-ball structure is established prior technique.
6. Julin–Juutinen and Crescimbeni–Forzani–Perini are the specific prior methods explained above, not publications of the exact fitted theorem.

The source family path inventory, README, main file and bibliography contain one manuscript and no companion claiming the viscous theorem. This is a bounded exact-prefix check, not a claim about every manuscript or every external paper. Broad search results for p-Laplace Hamilton–Jacobi source equations do not establish anything about the present principal part and were not used as theorem substitutes. Search misses have no priority force.

## 6. Advancement and final decision

The theorem removes the proposed finite-positive epsilon/lambda limit obstruction, provided that the upstream blow-up procedure actually supplies a locally uniform limit with FIT. It is a qualitative theorem at each fixed tau. It establishes neither that upstream procedure for p-harmonic solutions, nor a p-uniform gradient estimate, nor p-to-infinity gradient convergence. The unbounded epsilon/lambda regime loses time ellipticity in its divided PDE; Delta_x V=0 plus FIT still admits sin t. No uniform parameter estimate rescues that regime here.

Thus there is a concrete local advance within the exploratory program, but it does not settle the earlier gradient problem or produce a separate named-open-problem resolution. That limitation is not alone the reason for rejection: the decisive point is the technical character of the additional proof over the stipulated envelope package and the established autonomous monotone-divergence machinery.

**Disposition: TECHNICAL; record the finite-tau theorem and asymmetric local contact lemma as useful technical results if correctness passes independently. Do not nominate or count either, or the drift corollary, as the tenth substantial finding.** No exact prior publication was established, so KNOWN would overstate the evidence. Importance is resolved negatively under the requested standard; it is not left UNRESOLVED merely because worldwide priority cannot be certified.
