# I234 — local regularity: analytic record

**Verdict: NOT CLOSED.** No estimate for every bounded continuous viscosity solution on an interior product cylinder is proved here. No nonaffine entire counterexample with the full shear-fit hypothesis is produced. The results below are calculations and limited auxiliary statements, not a tenth finding. In particular, a smooth-solution calculation is not passed off as a viscosity regularity theorem.

## 1. Target, convention, and checked source contract

Fix an integer d>=1 and tau>0. Write Q_r=B_r^d x (-r,r). The desired statement is: for each M<infinity there are K=K(d,tau,M)<infinity and a modulus omega_(d,tau,M)(s) tending to zero with s, such that every V in C(Q_1) with osc_(Q_1)V<=M solving

    G_tau[V]=V_tt+2 D_xV.D_xV_t+D_xxV[D_xV,D_xV]+tau Delta_xV=0

has classical spatial derivatives on Q_(1/2), |D_xV|<=K there, and

    |D_xV(z)-D_xV(z')|<=omega_(d,tau,M)(|z-z'|).

The convention is G_tau[phi]>=0 at upper C^2 contacts, and <=0 at lower contacts, with every space-time test included. There is no exceptional zero-gradient definition: the operator is continuous and A(0)=diag(tau I,1). A modulus just for spatial separation at a fixed time would not by itself compare the two generally different times in the parent's blowdown; the formulation above supplies the modulus it actually uses.

The pinned source 01-introduction.tex, thm:main, concerns exact infinity-harmonic functions. The actual thm:liouville in 03-reduction.tex concerns the entire equation F[V]=0 without the trace term, with the all-center/all-radius fits stated in the brief. Neither contract includes G_tau. The source's q=a-|p|^2/2 is an unrestricted reparameterization. The pinned contracts are accepted as true, not audited. No source 04–08 operation is invoked with altered PDE input.

For later comparison, affine coordinate changes and affine subtractions preserve contact sides. If V solves G_tau=0, then V(x+at,t)-a.x-|a|^2t/2 also solves it, as does V(Rx,Rt)/R for R>0 and V+ct+C. Indeed pulling a C^2 test back by the invertible affine coordinate map gives the required test of V, and the classical chain rule gives, respectively, the same operator and R times the operator. This proves the viscosity version of these invariances; it does not differentiate V.

## 2. Algebra and loss of global ellipticity

In the (x,t) ordering put p=D_xV, q=V_t, b=(p,1). Then

    A(p)=b tensor b+diag(tau I,0),
    A(p)[(xi,eta)]=tau|xi|^2+(p.xi+eta)^2.

A is positive definite at every finite p, independently of q. But for |p|=P>0, evaluate on the unit vector (p/P,-P)/sqrt(1+P^2). The value is tau/(1+P^2). Thus there is no positive lower ellipticity constant uniform in p. Also tr A=1+|p|^2+d tau. Once |p|<=P is known, an explicit valid lower bound is

    A(p)[(xi,eta)] >= (|xi|^2+eta^2) / max(2,(1+2P^2)/tau).

This follows from eta^2<=(2)(eta+p.xi)^2+2P^2|xi|^2. The missing step is the bound P, not a matrix identity.

For smooth V let h=|p|^2/2 and w=q+h. Then G_tau=0 is

    (partial_t+p.D_x)w+tau div_x p=0.

The gradient Hessian of exp((q+|p|^2/2)/tau) equals a positive scalar times A(p). More precisely its quadratic form is exp(w/tau)[(eta+p.xi)^2/tau^2+|xi|^2/tau]. This is strictly positive, but the scalar can also tend to zero when q tends to -infinity. Neither uniform ellipticity nor coercivity in the full gradient follows. Assigning the density m=exp(w/tau) to a merely continuous viscosity solution is itself unjustified before derivatives exist.

## 3. What the primary literature actually provides

Sanchez Morgado's equation (4), at H(p)=|p|^2/2 and k=1/tau, is this equation (the paper takes integer k). Lemma 1 and Theorem 1 are for smooth functions on the space-time torus. Their periodic maximum construction and continuation do not supply an interior Dirichlet approximation of an arbitrary continuous local solution. The potentially degenerating eigenvalues are explicitly noted before Lemma 1.

Porretta's equation (1.7) becomes G_tau[V]=0 on setting u=-V and epsilon=tau. For the quadratic Hamiltonian, zero external potential and f=0, Theorem 3.4 assumes a smooth solution on a convex spatial domain, its lateral Neumann condition and the two nonlinear time-boundary conditions. Its constants involve the W^(1,infinity) norms of tau log m_0 and tau log m_1. In its proof the time-derivative maximum principle and the marginal data supply information at a maximum of the Bernstein quantity. Proposition 7.2 uses an already obtained full gradient bound. Theorem 6.5 is a weighted estimate local in time for the global smooth planning solution; it does not state an unweighted interior product-cylinder gradient estimate. These are genuine regularity results with additional inputs, not the requested local viscosity theorem.

Munoz's introduction independently identifies the same boundary-dependent route: control the time derivative using terminal density information, then apply Bernstein and classical elliptic regularity. Its word 'local' refers to the coupling of the MFG system, not to an arbitrary interior cylinder theorem. Only introduction/formulation pages 1–4 were read; no general theorem with all of its later hypotheses is imported.

## 4. Route A: the precise Bernstein calculation and the localization debt

All computations in this section assume V is C^3. Define the linearized operator

    L f=A(p):D^2 f+2 D_xw.D_x f,
    E=|D_xw|^2+tau|D_xxV|_F^2,
    k=q+|p|^2=w+h.

Differentiating G_tau yields L(V_i)=0 for each space-time derivative V_i, since the derivative of A in a spatial-gradient direction contracts with D^2V to 2D_xw. Product rules give

    Lq=0,  Lh=E,  LV=2p.D_xw,
    L(V^2/2)=tau|p|^2+k^2+2V p.D_xw.                 (A1)

For z=q+(3/2)h+lambda V^2/2 and |V|<=M,

    Lz=(3/2)E+lambda(tau|p|^2+k^2)+2lambda V p.D_xw.

Choose 0<lambda<=min(1,3tau/[8(1+M^2)]). Young's inequality, with coefficient 3/4 on |D_xw|^2, proves the pointwise inequality

    Lz >= (3/4)E+lambda k^2+(lambda tau/2)|p|^2.    (A2)

No gradient or Hessian bound was used in deriving this inequality. It is nevertheless an inequality for derivatives of an already smooth solution.

### 4.1 Fully paid limited consequence: smooth spatially periodic slabs

Suppose in addition that V is spatially periodic and C^3 on a neighborhood of T^d x [0,T], solving G_tau=0 there and |V|<=M. For any a>6/lambda set

    phi(t)=a(t^(-2)+(T-t)^(-2)),   L0=lambda M^2/2.

Then

    V_t+(3/4)|D_xV|^2 <= phi(t)+L0,   0<t<T.       (A3)

Proof: if z-phi has a maximum larger than L0, it is attained at an interior time, by the blowup of phi and boundedness of z on the closed slab. Spatial periodicity removes a lateral boundary. At that maximum D_xz=0 and A:D^2z<=phi''. Also

    k=z+(1/2)h-lambda V^2/2 > phi.

Consequently (A2) implies lambda phi^2<phi''. But phi''=6a(t^(-4)+(T-t)^(-4))<=6phi^2/a, a contradiction. Thus z<=phi+L0, and dropping its nonnegative lambda V^2/2 proves (A3).

This is an elementary specialization of the weighted, local-in-time mechanism in Porretta, not a new unweighted local theorem. It controls w+h/2, hence an upper bound on w, but permits q to be very negative. It does not bound h alone. Translating u=-V gives the sign of Porretta's weighted estimate exactly.

### 4.2 Why this argument is not a product-cylinder estimate

On a product cylinder one must exclude lateral maxima too. For an additive barrier Phi(x,t), at an interior maximum of z-Phi the exact consequence of (A2) is

    (3/4)E+lambda k^2+(lambda tau/2)|p|^2
      <= tau Delta_xPhi+D^2Phi[b,b]+2D_xw.D_xPhi.  (A4)

The last term absorbs into part of E at the cost C|D_xPhi|^2. The middle term contains D_xxPhi[p,p], which grows with |p|^2. For Phi=phi(t) these spatial terms vanish, which is the crucial simplification in (A3). For a spatial barrier blowing up as L dist(x,boundary)^(-a), |D_xPhi|^2/Phi^2 grows as dist^(-2), and |D_xxPhi|/Phi also grows as dist^(-2). Merely enlarging L does not turn (A4) into a contradiction uniformly near that boundary. This is a failure of this direct barrier choice, not proof that every localization is impossible.

Using a multiplicative cutoff on h instead has an equally explicit issue: at a positive maximum of eta h,

    0 >= eta E+h A:D^2eta+2h D_xw.D_xeta
                -2(h/eta) A[Deta].               (A5)

Indeed L(eta h)=eta Lh+h Leta+2A[Deta,Dh] and Dh=-(h/eta)Deta at the maximum. The h A:D^2eta and h A[Deta]/eta terms can be order h^2, while absorbing 2h D_xw.D_xeta also costs order h^2. E is a Hessian quantity with no positive lower bound in h alone. Affine solutions have E=0 with arbitrarily large h. Their oscillation grows too, so this is not a counterexample to the target, but it rules out an algebraic inference E>=c h^2 for all solution jets.

A useful lower-density input w>=-K would make k=w+h large when h is large. The requested hypotheses do not supply that input, even as a defined pointwise quantity. I do not assume it or substitute an upper bound on w for it.

### 4.3 Two-point route and its own unpaid localization

Without a cutoff, a doubled maximum of V(z)-V(z')-psi(|z-z'|) has matching full gradients, so A has matching coefficients. In the model case this supports a maximum-principle argument on a space-time torus. On a bounded cylinder a localization term separates the gradients and introduces matrix errors depending on them.

In particular, positive definiteness alone does not justify taking a negative curvature contribution with unit coefficient after changing variables by A^(1/2). If D<=0 and e^TDe<=-c, the general trace bound is

    tr(AD)<=-c/(e^T A^(-1)e),

as follows by applying the positive matrix -A^(1/2)D A^(1/2) to A^(-1/2)e. The denominator need not be uniformly bounded here. For example D=-c ee^T obeys the two assumed inequalities but tr(AD)=-c e^TAe, which can have arbitrarily small magnitude for the matrices in Section 2. Accordingly I do not transplant the unweighted trace inference in Sanchez Morgado's displayed (9)–(10) into a local proof. This observation does not audit the pinned results or disprove the separate periodic existence assertion.

## 5. Route B: what the exact shear fits give by themselves

Assume the full fit condition in the brief with constant C0, and assume |V|<=M on Q_1 after a constant subtraction. The following are value estimates, not gradient estimates. Fix a center in Q_(1/2) and r0=1/4. Write its fit coefficients as p_r,q_r. Taking opposite horizontal increments of length r0 gives

    |p_(r0)|<=M/r0+C0.

At dyadic radii r_j=2^(-j)r0, comparing the two fits on the t=0 slice gives

    |p_(rj)-p_(r(j-1))|<=3C0,
    |p_(rj)|<=M/r0+C0+3C0 j.                     (B1)

These arguments use the same center but need no differentiability or PDE. For r_(j+1)<|h|<=r_j, use the r_j fit at l=0, obtaining uniformly

    |V(x+h,t)-V(x,t)|<=C(M+C0)|h|(1+log(r0/|h|)). (B2)

Time coefficients can also be bounded without evaluating V outside Q_1. Set s0=r0/(1+|p_(r0)|) and evaluate its fit at (h,l)=(0,s0); this lies in the fitted box and Q_1. Then |q_(r0)|s0<=2M+C0r0. To compare consecutive q's use

    s_j=r_j/(1+|p_(rj)|+|p_(r(j-1))|),  h=0.

Both fits apply there and yield

    |q_(rj)-q_(r(j-1))|
       <=3C0(1+|p_(rj)|+|p_(r(j-1))|).

Consequently |q_(rj)|<=C(M,C0)(1+j)^2. If l is sufficiently small, choose a dyadic r_j comparable to

    C(M,C0)|l|(1+log(r0/|l|))

with the constant large enough that |p_(rj)l|<=r_j. Evaluating at (0,l) yields the local uniform value modulus

    |V(x,t+l)-V(x,t)|<=C(M,C0)|l|(1+log(r0/|l|))^2. (B3)

For the remaining non-small increments use |V|<=M. Thus the normalized all-fit family is equicontinuous with quantitative moduli. But the increments in (B1) are bounded, not summable; no limiting fitted slope or classical derivative follows. Horizontal O(r) fits alone admit the familiar x log|x| obstruction at the origin. This observation is only about the horizontal subcondition; x log|x| is NOT asserted to satisfy the full space-time shear fits or the PDE. I found no argument extracting the missing derivative modulus from the full fits and G_tau together.

## 6. Route C in one spatial dimension: a hodograph identity, not regularity

For d=1 suppose V is C^2 and det D^2V is nonzero near a point. The gradient map (x,t)->(p,q) is locally invertible. Its local Legendre transform U(p,q)=xp+tq-V has D^2U=(D^2V)^(-1). Multiplying G_tau[V]=0 by det D^2U gives

    U_pp-2p U_pq+(p^2+tau)U_qq=0.

Set r=q+p^2/2 and U(p,q)=W(p,r). Direct differentiation gives

    W_pp+tau W_rr+W_r=0.                         (C1)

This is a constant-coefficient elliptic equation on the unknown gradient-image domain. It is a genuinely different calculation from Bernstein. It does not prove a local estimate in the original variables: the inverse map requires a nonzero Hessian determinant, and its image can escape to infinity or lack a controlled interior radius. Oscillation of V does not establish those prerequisites. Higher dimensions do not give this two-by-two linear cofactor reduction. No general convexity of V is assumed or available (indeed the nonzero two-dimensional Hessian of a solution must be indefinite).

## 7. Active checks and exact unpaid obligations

The simplest potential counterexamples fail directly. For V=f(x_1)+g(t) with C^2 f,g the equation is g''+(f'^2+tau)f''=0; each term depends on a different variable, so they are opposite constants. For a travelling profile V=f(x_1+a t)+bt, the equation is ((f'+a)^2+tau)f''=0, so f is affine. Arbitrary temporal functions are not solutions: V=g(t) requires g''=0. The bounded-forcing transverse oscillations from I224 are not examples for G_tau=0 because the tau Delta_x term does not vanish. None of these checks rules out more complicated nonsmooth examples.

The unresolved steps are explicit:

* **A, local a priori estimate:** establish, on a strictly interior product cylinder, a spatial Lipschitz bound and common space-time modulus of D_xV for all smooth solutions, with constants depending only on d,tau and osc V. (A4) or (A5) has not been closed using just these data. One may instead first establish an appropriate lower-density/time-derivative bound, but that is itself unpaid.
* **B, viscosity bridge:** establish local approximation of each bounded continuous viscosity solution by a class to which those estimates apply, or prove the estimates directly by viscosity methods. Existence of one smooth solution for the global planning/periodic problem does not imply that approximation. Strict convexity proves uniqueness within an appropriate finite-energy weak class after the weak formulation is available; it does not identify every continuous viscosity solution with that class.
* **Alternative fit-restricted step:** show that G_tau plus the full fits improves (B1) to convergent slopes with a common modulus, or supplies a class-specific substitute for A and B. The logarithmic value moduli (B2)–(B3) do not do this.

If B is supplied and a common derivative modulus is already known for the approximants, passage to the limit is elementary and fully valid: bounded equicontinuous D_xV_j have a uniformly convergent subsequence on each smaller compact cylinder; integrate the derivatives on spatial line segments and pass to the limit in V_j to identify their limit with the classical D_xV. This proves the same modulus for V. It clarifies exactly what a regularization argument would have to deliver rather than presuming its conclusion.

The parent's final comparison of fixed points by blowdown would then apply. Here A and B, or their fit-restricted alternative, remain unpaid. No statement about worldwide novelty or an accepted-count change is made.
