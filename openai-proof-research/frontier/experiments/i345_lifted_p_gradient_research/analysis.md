# I345 — unrestricted actual-p gradient estimate by a constrained lift

2026-10-13. Research candidate, subject to an independent full proof and contribution gate. The pinned OpenAI corpus at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is stipulated true. I344 and the internal I236/I241 arguments are independently checked inputs, not stipulations. No numerical experiment is used.

## 1. Claim and inputs

**Theorem.** For every integer n>=2 there are alpha_n in (0,1/3] and C_n<infinity such that, for every finite p>=3, every bounded weak solution u in W^{1,p}_loc(B1) of

    integral |Du|^{p-2} Du.Dphi = 0,   phi in C_c^infinity(B1),

has its continuous representative in C^{1,alpha_n}(B1/2), and

    ||Du||_infinity(B1/2)+[Du]_{alpha_n;B1/2} <= C_n osc_B1 u.       (T)

There is no assumption on the sign, critical points, level-set geometry, gradient modulus, or boundary data. The constants depend only on n; neither their values nor an endpoint exponent are identified.

External inputs, with actual interfaces checked in the reading ledger, are Kotschwar–Ni Theorem 1.1; weak/viscosity equivalence for the homogeneous p-Laplace equation (Julin–Juutinen, introduction, Definitions 2.1–2.3 and Theorem 3.1); Uhlenbeck's scalar regularity theorem, quantitative Theorem (5.4), its proof and Bernstein Theorem (6.1); Savin Theorem 1.3 with the parameter-uniform proof of Proposition 4.1; and classical linear divergence-form solution Harnack. Pinned inputs are the infinity estimate `01, thm:main`, the infinity lift `02, lem:linear-lift`, the geometric selection/comparison/extraction and derivative extraction in `03`, the equation-free fit tools in `04`, and the geometric barycentric-envelope operations in `05`. We do not use the infinity three-point estimate for p-solutions. The finite-positive-viscosity fitted-class theorem is revalidated in Section 9.

Convention: operators with positive Hessian sign are >=0 at upper tests and <=0 at lower tests. Write X[v]=v^T Xv. “p-harmonic” always refers to the continuous representative of an actual weak solution, not merely a function satisfying an arbitrary limiting equation.

## 2. Uniform Lipschitz bounds and uniform qualitative flatness

### 2.1 The logarithmic estimate

Let v>0 be p-harmonic in a Euclidean ball B_R, and w=-(p-1)log v. Set the auxiliary parameter in Kotschwar–Ni Theorem 1.1 to 1/2 and its curvature bound to zero. For p>=3 its negative-part term in c_{p,n} vanishes, so

    c_{p,n}=(p/2+1)(p-1),
    b_{p,n}=2(p-1)/(n-1)-2,
    C(n,0,p,R,1/2)=[20(n+p-2)(n-1)+10(p-1)(n-1)]/R^2.

The theorem therefore gives |Dw|^2 <= K_n(p-1)^2/R^2 on B_R/2. Dividing by (p-1)^2 gives |Dlog v|<=K'_n/R. For a bounded signed solution with M=osc u>0, use

    v=u-inf u+M,    M<=v<=2M.

Translation preserves its weak equation, and |Du|=v|Dlog v|<=2K'_n M/R. M=0 is immediate. The theorem concerns positive p-harmonic functions; classical scalar C1 regularity gives the continuous differentiable representative, and smoothness is needed only on the open noncritical set in the gradient-estimate proof. Critical points have zero gradient. No regularized equation with different constants is inserted.

After normalizing M<=1 and u(0)=0, there is one Lipschitz constant on B_7/8 for all p>=3. The affine lifts

    U(y,b)=u(y)+b,   (y,b) in B1^n x R,

are uniformly bounded and L-Lipschitz on B_7/8^{n+1}. They satisfy the exact increment U(z+h xi)=U(z)+h, xi=e_b.

### 2.2 Classical compact-p interface

For each finite P>=3, Uhlenbeck's estimate (5.4), with rho(Q)=Q^s, s=(p-2)/2 in [1/2,(P-2)/2], gives common C^{1,theta(n,P)} bounds on compact interior balls for 3<=p<=P, once |Du| is bounded. Here Q=|Du|^2, C=0, and rho+2Qrho'=(p-1)Q^s. Conditions (1.3)–(1.4) have common K and a positive fixed continuity exponent a<=min(1/2,2/(n-2)) (omit the second restriction for n=2). Indeed

    |s Q1^s-s Q2^s| <= K (Q1+Q2)^{s-a}|Q1-Q2|^a

follows by homogeneity and the uniform a-Hölder bound for t^s on [0,1] for this compact s interval. Choose a strictly smaller exponent if needed at a displayed endpoint.

This uniformity is a reading of the quantitative proof, not the unjustified statement that every function C(p) is bounded on compact intervals. Sections 3–5 use common ellipticity K, this common continuity modulus, bounded powers of 2, bounded s+1 and their reciprocals, and fixed powers of the chosen radius. In (4.11) choose the perturbation radius first, then its smallness threshold using the largest s. In (5.4) choose the decay parameter once to satisfy its inequalities for all these s. The resulting exponent from (5.5) and constant have one positive/common choice. The prior Lipschitz bound supplies M in (5.4). For original dimension two, one can extend u constantly in an inactive third coordinate; this preserves the actual weak p-equation, and the three-dimensional estimate restricts back to the plane. This is distinct from adjoining a linear coordinate. For one fixed p, Theorem (6.1), or directly scaling (5.4) on arbitrarily large balls, makes an entire locally weak solution with bounded gradient affine; no finite total energy on R^n is required.

### 2.3 Expanding-domain proof, including n=2

We prove a common o(r) Euclidean affine-fit error at interior centers. Otherwise there are normalized u_i, p_i>=3, centers y_i in B_3/4 and r_i->0 such that the functions

    f_i(Y)=[u_i(y_i+r_iY)-u_i(y_i)]/r_i

stay a fixed positive distance on B2 from every linear function. Their domains exhaust R^n. On each fixed ball the uniform original Lipschitz bound gives |f_i(Y)|<=L|Y| and Lipschitz constant L. Diagonal Arzelà–Ascoli gives an entire L-Lipschitz limit f with f(0)=0.

After a subsequence, p_i tends to a finite p_*>=3 or to infinity. Set epsilon_i=1/(p_i-2). Every u_i solves the continuous polynomial viscosity equation

    D^2u[Du]+epsilon_i |Du|^2 Delta u=0.                  (P)

At nonzero test gradient this is a positive multiple of the p-Laplacian. At zero gradient both this operator and the continuous p-Laplacian (p>2) vanish. Weak/viscosity equivalence and the standard strict-contact argument apply. Consequently f solves (P) with epsilon_* if p_* is finite, and is an infinity-harmonic function if p_i->infinity. In the finite case, equivalence returns an actual weak p_*-solution, and Uhlenbeck (6.1) makes f affine.

In the infinite case, lift f to F(Y,b)=f(Y)+b. The pinned infinity lift applies in every original dimension; F is globally Lipschitz and infinity-harmonic in dimension n+1>=3. On B_R its oscillation is at most 2 Lip(F)R. Scaling the pinned interior estimate gives

    [DF]_{alpha;B_R/2} <= K Lip(F) R^{-alpha}.

For each fixed pair of points let R->infinity: their gradients agree. F and hence f are affine. This also handles original dimension two without an unstated planar source theorem. Both alternatives contradict the unit-scale error. Notice that we used global entire-limit rigidity, not gradient convergence from value compactness.

The same conclusion holds for U_i after lifting: add the exact b coordinate to a linear fit of f_i. Thus the common Euclidean affine-fit modulus implies cylinder goodness at every fixed positive parameter when r is sufficiently small.

## 3. Correct viscosity lift

Let Pi=I-xi tensor xi, epsilon=1/(p-2). Then U solves

    L(DU,H)=H[DU]+epsilon |Pi DU|^2 tr(Pi H)=0.          (L)

This does not claim that U is p-harmonic.

Proof at an upper test phi at (y0,b0): shift this point to zero. Restriction to the b line gives phi_b=1 and H_bb>=0. Put g=D_y phi. For sigma>0 replace phi by phi_sigma=phi+sigma b^2/2. It is still an upper test. The implicit function theorem, since (phi_sigma)_bb=H_bb+sigma>0, gives a local C1 branch b=b(y) solving (phi_sigma)_b=1, with b(0)=0. The function

    psi(y)=phi_sigma(y,b(y))-b(y)

is C2, touches u from above, has gradient g, and Hessian

    K=H_yy-H_yb H_by/(H_bb+sigma).

It is an upper test because phi_sigma>=u(y)+b for all nearby pairs, including this branch. Define H_sigma=H+sigma xi tensor xi. The block matrix

    H_sigma-diag(K,0)

is positive semidefinite: it is the outer product of (H_yb,H_bb+sigma) divided by H_bb+sigma. The matrix

    M=(g,1) tensor(g,1)+epsilon |g|^2 Pi

is positive semidefinite, and its yy block is g tensor g+epsilon |g|^2 I. Therefore

    tr(M H_sigma) >= tr((g tensor g+epsilon|g|^2 I)K) >=0.

Let sigma decrease to zero; M stays fixed and tr(M H_sigma)->tr(MH). This proves the upper inequality even when H_bb=0; there is no need for convergence of K. When g=0 the right side is zero and M=xi tensor xi, so the vertical curvature alone is sufficient. For lower tests use phi-sigma b^2/2, H_bb-sigma<0, and the negative semidefinite block comparison. This proves the reverse inequality. All tests, including critical original gradients, have been treated.

## 4. Cylinder selection and geometric compactness

Use source `03`'s cylinder, goodness, beta and b(s) definitions in dimension N=n+1, with G=B_3/4^N, D(z)=dist(z,partial G), and the family of all normalized actual-p lifts, p>=3. Explicitly a fit is

    |U(z+h)-U(z)-P.h|<=lambda r
    for |h.N_P|<=r, |h-(h.N_P)N_P|<=sqrt(lambda)r.

For every such fit, its inscribed ball gives

    |P|<=L+sqrt(lambda),   |P.xi-1|<=sqrt(lambda).       (4.1)

In particular all sufficiently accurate fits have 1/2<=|P|<=L+1. Section 2.3 gives b(s)->0: failure produces r_i<=s_iD(z_i)->0 with a bad lambda_i>=delta, while an affine limit with added-coordinate slope exactly one gives error <delta r_i on B_2r_i. This makes lambda_i good, a contradiction.

Suppose b has no positive power bound. The equation-free running-maximum construction in `03, lem:bad-scales` can be strengthened by requiring its truncated approximate maximum to exceed i. We obtain gamma_i->0, s_i->0 and bad lambda_i with

    b(s)/s^{gamma_i} <= 2 b(s_i)/s_i^{gamma_i},  s_i<=s<=1/8,
    b(s_i)/s_i^{gamma_i} >= i,
    b(s_i)/4 < lambda_i <= b(s_i),   r_i<=s_iD(z_i).     (4.2)

All selections are approximate suprema; goodness need not be monotone. For every fixed integer k,

    s_i/lambda_i^k <= (4/i)^k s_i^{1-k gamma_i} ->0.     (4.3)

At every fixed multiple of r_i and every center a fixed multiple of r_i from z_i, Lambda lambda_i, Lambda=32, is good eventually, exactly as in the source: beta<=b(2Ms_i)<=8lambda_i(2M)^{gamma_i}<32lambda_i.

If the selected p_i has a bounded subsequence, Section 2.2 gives uniform Euclidean Taylor error C r^{1+theta}. The nonzero slope DU=(Du,1) makes every lambda>C r^theta good, so lambda_i<=C r_i^theta<=C' s_i^theta. But (4.2) gives lambda_i>i s_i^{gamma_i}/4, impossible for gamma_i<theta. Hence it suffices to treat p_i->infinity and epsilon_i->0.

Choose P_i for the base good Lambda lambda_i fit and rotate it to c_i e_N. Define V_i by

    U_i(z_i+r_i(sqrt(lambda_i)x,t))
       =U_i(z_i)+r_i c_i[t+lambda_i V_i(x,t)].          (4.4)

The domains exhaust R^n x R. Everything used to obtain boundedness, equicontinuity, inherited fits and nonaffinity in `03, prop:nonaffine-limit` is geometric except its separate PDE passage. Its hypotheses have now been paid. For precision, the needed comparisons and limits are these:

* Equal-parameter concentric fits at comparable radii give direction/vector differences O(sqrt(lambda_i)) and norm differences O(lambda_i), by evaluation on a common ball and then a short common axial segment. Their norms have the lower/upper bounds (4.1).
* Chain these comparisons from r_i to Rr_i for each fixed R. The direction difference is O(sqrt(lambda_i)(1+log R)) and the norm difference O(lambda_i(1+log R)). For any compact normalized box choose a fixed R much larger than K(1+log R); its physical image lies in the quarter margins of that enclosing cylinder.
* Compare fits at every center in this box and at fixed radius Sr_i, using the displaced-center comparison and a finite chain of radii. In the base coordinates their coefficients satisfy P_x=O_{K,S}(sqrt(lambda_i)), P_t-c_i=O_{K,S}(lambda_i). Thus p_i'=P_x/(c_i sqrt(lambda_i)), q_i'=(P_t/c_i-1)/lambda_i are bounded.
* These fits imply local boundedness of V_i. Their normalized domains contain

      |ell|<=S/2, |h-p_i' ell/(1+lambda_i q_i')|<=S,

  and their value error is <=Lambda S/c_i<=2Lambda S. Given any accuracy, first make S small, then make increments small relative to the bounded p_i',q_i'. This proves local equicontinuity without any first-jet bounds on V_i. A diagonal subsequence converges locally uniformly to V with V(0)=0.
* For a fixed limiting center and R choose S=4R, pass a subsequence of bounded fit coefficients, and use the strict domain margins. V has at every center and every R a fit

      |V(x+h,t+ell)-V(x,t)-p.h-q ell|<=C0 R,
      |ell|<=R, |h-p ell|<=R,   C0=8Lambda.            (FIT)

  The auxiliary coefficient subsequence may depend on this center and radius; V is already fixed. Write q=a-|p|^2/2 to match the source theorem.
* If V=p.x+qt were affine, the physical slopes c_i(sqrt(lambda_i)p,1+lambda_i q) would have lambda_i cylinders in a fixed normalized box. Their residual is o(lambda_i r_i). They are nonzero, making the selected bad lambda_i good. Thus V is nonaffine.

No PDE assertion from the source's original extraction is imported. The exact replacement follows.

## 5. Rescaled PDE, jet constraint and bounded negative viscosity

In the rotated coordinates write xi_i=(a_i,b_i), |a_i|^2+b_i^2=1; set beta_i=1/c_i, A_i=1-beta_i^2 and S_lambda=diag(I,sqrt(lambda)). For any test of V_i the physical gradient is c_i q_i, where

    q_i=(sqrt(lambda_i)D_x phi,1+lambda_i phi_t).

The exact affine increment in xi_i implies at both upper and lower tests

    q_i.xi_i=beta_i.                                    (5.1)

The physical Hessian is (c_i/r_i)S_lambda D2phi S_lambda. Direct substitution in (L), divided by the positive lambda_i c_i^3/r_i, gives

    D2phi[(D_x phi,1+lambda_i phi_t)]
       + C_i(Dphi) tr(S_lambda Pi_i S_lambda D2phi)=0,

    C_i(q)=nu_i+epsilon_i(2q_t+|q_x|^2)
                     +epsilon_i lambda_i q_t^2,
    nu_i=epsilon_i A_i/lambda_i.                         (5.2)

The formula uses (5.1), since

    |Pi_i q_i|^2=A_i+lambda_i(2phi_t+|D_xphi|^2)
                                      +lambda_i^2 phi_t^2.

It is an on-test identity; it is not an identity for arbitrary jets.

Here is a globally elliptic operator with which stability is legitimate: replace C_i(q) in (5.2) by max(C_i(q),0). It agrees at every test of V_i, where C_i=epsilon_i|Pi_i q_i|^2/lambda_i>=0. Its coefficient matrix is an outer product plus a nonnegative multiple of S_lambda Pi_i S_lambda. Thus V_i really is a solution of this continuous extension.

To control negative nu_i, use local boundedness of V_i on a fixed closed unit ball. If |V_i|<=M there, V_i-K|z|^2 with K>2M+1 has a maximum in its interior. The associated quadratic upper test has gradient bounded by 2K, independently of i. At that contact the preceding nonnegative identity gives A_i>=-C_M lambda_i. Consequently

    nu_i >= -C_M epsilon_i ->0 from below.              (5.3)

This argument does not assume that every point has a bounded test gradient. One bounded contact is enough, because A_i is a sequence parameter, not a pointwise field.

The exact increment also gives, on all admissible translated points,

    V_i(z+s w_i)=V_i(z)+s delta_i,
    w_i=(a_i,b_i sqrt(lambda_i)),
    delta_i=(beta_i-b_i)/sqrt(lambda_i).                 (5.4)

To bound delta_i choose s=1/|w_i| at the center of a fixed larger normalized ball. Local boundedness gives |delta_i|<=C|w_i|. Thus delta_i is bounded, and delta_i->0 if a_i->0. After subsequences a_i->a, b_i->b, delta_i->delta, local uniform convergence passes (5.4) to

    V(x+s a,t)=V(x,t)+s delta.                          (5.5)

In particular a.D_xV=delta is an exact transport identity; it is not an unproved differentiability assertion.

## 6. Finite effective viscosity and exact projected fits

If nu_i has a bounded subsequence, (5.3) yields nu_i->nu>=0. The extended operators of Section 5 converge uniformly on compact jet sets to

    F_nu,a(q,X)=X[(q_x,1)]+nu tr((I-a tensor a)X_xx).

Indeed epsilon_i,lambda_i->0, S_lambda Pi_i S_lambda tends to diag(I-a tensor a,0), and max(C_i(q),0)->nu. Strict-contact viscosity stability therefore proves F_nu,a[V]=0. This supplies the missing off-constraint compactness interface.

If a=0, then delta=0 and this is G[V]+nu Delta_xV=0. FIT and either the pinned Liouville theorem (nu=0) or Section 9 (nu>0) make V affine.

If a!=0, put e=a/|a| and k=delta/|a|. Equation (5.5) gives exactly

    V(se+y,t)=k s+W(y,t),   y in e^perp.

A test ks+psi(y,t) is a genuine test of V, and its Hessian annihilates e. Both the rank-one Hessian term and the trace reduce to

    D2W[(D_yW,1)]+nu Delta_yW=0.                        (6.1)

This reduction is valid in viscosity form, including all critical horizontal gradients. The parallel gradient component drops out because the Hessian, not merely its quadratic form in one direction, annihilates e.

The fits project **with the same constant**, without the radius enlargement proposed in I344. Given any original fit p=d e+p_perp and ordinary time coefficient q at (se+y,t), use increments

    h=d ell e+h_perp,
    |ell|<=R, |h_perp-p_perp ell|<=R.

They belong to the original sheared box. Subtracting the exact term k d ell gives

    |W(y+h_perp,t+ell)-W(y,t)-p_perp.h_perp
                       -(q+d^2-k d)ell|<=C0 R.        (6.2)

This is precisely FIT for W, with ordinary time coefficient q'=q+d^2-kd; the source's a' is q'+|p_perp|^2/2. No uniform bound on d or k is necessary for this projection. For completeness, horizontal increments in e at ell=0 give |d-k|<=C0. For zero transverse dimension (if applying the lemma outside the present n>=2 setting), (6.1) is W_tt=0 directly. Otherwise the pinned/Section 9 Liouville theorem applies. Again V is affine, contradicting Section 4. Every finite-nu branch is excluded, including original near-critical slopes.

## 7. Uniform lifted small-solution estimate

We prove a new cylinder estimate for (L), not quote I241's different polynomial equation. Suppose a fit has slope P=c e_N, c in [1/2,L+1], parameter eta, radius H, and

    A=1-c^{-2}>0,    e=epsilon A,    0<e<=1.

For sufficiently small eta, (4.1) implies xi=(a,b), b>=(1-sqrt(eta))/(L+1)>=b0>0. Put T_e=diag(sqrt(e)I,1) and

    ell=(H/4)sqrt(eta/e),
    U(z+ell T_e(x,t))=U(z)+c ell[t+e W(x,t)].           (7.1)

If eta/e<=1, this ellipsoid is strictly within the fitted cylinder and

    ||W||_B1 <= (4/c)sqrt(eta/e).                       (7.2)

On its constrained tests the equation becomes

    D2W[(D_xW,1+e W_t)]+B(DW) tr(S_e Pi S_e D2W)=0,
    B(q)=1+epsilon(2q_t+|q_x|^2)+epsilon^2 A q_t^2.     (7.3)

Here B=|Pi(sqrt(e)q_x,1+e q_t)|^2/A>=0 at physical tests. Replace B globally by max(B,0). This preserves the viscosity equation for W.

For proportional estimates include an amplitude d in [0,1]. The family is

    F_{epsilon,A,e,xi,d}(X,q)
      =X[(d q_x,1+e d q_t)]+max(B_d(q),0) tr(S_e Pi S_e X),
    B_d=1+epsilon(2d q_t+d^2|q_x|^2)+epsilon^2 A d^2 q_t^2.

One may allow epsilon,A,e independently in [0,1]; the actual parameters obey e=epsilon A. The family is continuous and elliptic for every Hessian and every gradient. It is polynomial on a common neighborhood |q|<rho, since B_d>=1/2 there. It vanishes at X=0. At q=0 its coefficient matrix is

    M0=e_N tensor e_N+S_e Pi S_e,
    M0[(h,s)]=s^2+|h|^2+e s^2-(a.h+b sqrt(e)s)^2.

Its spatial block is I-a tensor a>=b0^2 I. Its mixed block is -sqrt(e)b a, and its time block is 1+e|a|^2. The time Schur complement is **exactly 1**, since (I-aa^T)^{-1}a=a/b^2. Thus M0 has common positive lower and finite upper bounds for all parameter endpoints e=0, A=0, epsilon=0 and d=0. By continuity these bounds hold on a common small q ball. First and second jet derivatives are uniformly bounded on a common small (X,q) neighborhood. The nonsmooth max switch lies outside it and violates none of Savin's hypotheses.

Savin H1, H2, H4 are therefore met uniformly. His Proposition 4.1 proof works with varying operators having this common jet radius, ellipticity and C2 bounds; it supplies a common small-solution threshold sigma and finite C2 bound on B1/2 for this family. It does not assume a gradient bound on the unknown W. Make sigma smaller as necessary. If a0=||W||_B1<=sigma and a0>0, set d=a0/sigma and Z=W/d. Division of the equation by d gives exactly F_{epsilon,A,e,xi,d}(D2Z,DZ)=0. Its norm is sigma. Hence

    ||DW||_B1/2+||D2W||_B1/2 <= C a0.                  (7.4)

This amplitude step is essential: the unscaled theorem alone gives only an absolute small bound, insufficient for the final Hessian estimate. If a0=0 everything is immediate.

Choose eta/e<=d_* with d_* depending only on n,L, so (7.2) meets the threshold. Restoring physical variables yields on the half ellipsoid

    ||T_e D2U T_e|| <= (c e/ell) C (4/c)sqrt(eta/e)
                       <= C' e/H.                     (7.5)

The absolute small-gradient conclusion can be arranged to make the physical axial component c(1+e W_t)>=c/2. The actual gradient P_new=DU(z) is therefore nonzero. Its formula is c(sqrt(e)D_xW,1+eW_t), so |T_e^{-1}N_{P_new}| is uniformly bounded. For h in Z_lambda(0,r;P_new), if lambda<=e,

    |T_e^{-1}h| <= C r+sqrt(lambda/e)r <= C' r.

If r<=k_*ell its whole segment lies in the half ellipsoid. Taylor's formula and (7.5) then give

    sup_{Z_lambda(0,r;P_new)}
       |U(z+h)-U(z)-P_new.h| <= C e r^2/H.             (7.6)

This is a uniform estimate for constrained lifts of actual weak p-solutions at a value-fit slope. It assumes neither original noncriticality nor original differentiability beyond what follows from the small-solution theorem. Its nonzero total slope is supplied by the lift.

## 8. Infinite effective viscosity: repaired quadratic transfer

The only remaining subsequence is nu_i=epsilon_i A_i/lambda_i->+infinity. Then A_i>0 eventually. Set

    R_i=nu_i^2,   H_i=R_i r_i,
    kappa_i=K0(4R_i)^{gamma_i},   eta_i=kappa_i lambda_i,
    K0=64.                                             (8.1)

Since A_i<=1 and epsilon_i<=1, R_i<=lambda_i^{-2}. By (4.3), R_i s_i->0. Centers within 2H_i of z_i retain at least half its boundary distance. All radii up to H_i are admissible, and (4.2) gives

    beta(z,r)<=b(4R_i s_i)<=8lambda_i(4R_i)^{gamma_i}<eta_i.

Thus eta_i is good at each of these radii. Also eta_i<=C lambda_i^{1-2gamma_i}->0 and kappa_i/nu_i->0. We use eta_i throughout growing-scale comparisons; a fixed multiple of lambda_i is not asserted good on growing boxes.

### 8.1 Unequal-parameter comparison, the repair to I344

Let Q_{i,0} be an eta_i fit at the base radius r_i, and P_i the Lambda lambda_i fit used in (4.4). The common ball B_{sqrt(Lambda lambda_i)r_i} gives

    |P_i-Q_{i,0}| <= C kappa_i sqrt(lambda_i).

Consequently their axis angle is <=C kappa_i sqrt(lambda_i), tending to zero. This bound is larger than O(sqrt(eta_i)); the equal-parameter norm lemma cannot simply be applied to this pair.

Use instead a point on the base axis at distance t_i r_i, where t_i is a sufficiently small fixed constant times kappa_i^{-1/2}. This point belongs to both cylinders: its coarse transverse displacement is <=C t_i kappa_i sqrt(lambda_i)r_i<=sqrt(eta_i)r_i, while axial margins hold. The fit errors there give

    |(P_i-Q_{i,0}).N_{P_i}| <= C kappa_i^{3/2}lambda_i.

The angular correction is quadratic, <=C kappa_i^2 lambda_i. Therefore

    ||P_i|-|Q_{i,0}|| <= C kappa_i^2 lambda_i.           (8.2)

Chain eta_i fits through dyadic radii from r_i to H_i. The equal-parameter source norm comparison is now applicable at each step, because (4.1) supplies common slope norm bounds. For a final coarse slope Q_i,

    ||Q_i|-c_i|| <= C[ kappa_i^2 lambda_i
                          +eta_i(1+log nu_i)].          (8.3)

This replaces I344's unproved O(eta_i(1+log nu_i)) comparison between different-parameter base/coarse fits. A purely first-order vector comparison would be insufficient. The weaker **quadratic** comparison (8.3) is sufficient.

For c'_i=|Q_i| and A'_i=1-(c'_i)^{-2}, the scalar map is uniformly Lipschitz on [1/2,L+1]. Since A_i=nu_i lambda_i/epsilon_i,

    |A'_i-A_i|/A_i
       <= C epsilon_i [kappa_i^2+kappa_i(1+log nu_i)]/nu_i ->0.     (8.4)

Indeed kappa_i=K0 4^{gamma_i}nu_i^{2gamma_i}, gamma_i->0 and nu_i->infinity; eventually 4gamma_i<1/2. This estimate does not require a lower bound on the original |Du_i|. It proves A'_i>0, A'_i/A_i->1 and e'_i=epsilon_i A'_i asymptotic to e_i=nu_i lambda_i.

### 8.2 Applying the small-solution estimate on the available domain

The eta_i cylinder at radius H_i, slope Q_i, has e'_i>0 and

    eta_i/e'_i ~ kappa_i/nu_i ->0.

Its added-coordinate direction satisfies b'_i>=(1-sqrt(eta_i))/(L+1), so the common Savin family applies. Its inner ellipsoid scale is

    ell_i/r_i=(R_i/4)sqrt(eta_i/e'_i)
                  ~ (1/4)nu_i^{3/2}sqrt(kappa_i) ->infinity.

Furthermore lambda_i<=e'_i eventually. Hence (7.6) applies at the selected fine radius r_i. Its error divided by lambda_i r_i is

    C e'_i r_i/(lambda_i H_i) ~ C/nu_i ->0.

The actual fitted slope DU_i(z_i) is nonzero, so lambda_i is good. This contradicts its selection. All cylinders and ellipsoids lie in the original solution domain by (4.3). No wider-box bound on V_i and no inferred p-uniform gradient modulus were used.

Every selected branch has now been excluded. Thus b(s)<=B s^gamma for some B<infinity, gamma>0 and sufficiently small s, for the full p>=3 lifted family.

## 9. Independent validation of finite-positive-viscosity rigidity

We supply the internal input used in Section 6. For fixed 0<tau<infinity, let

    G_tau(q,X)=X[(q_x,1)]+tau tr_x X.

Every continuous entire solution with FIT for one finite C0 is affine. Constants here may depend on tau and C0; no tau-uniform local regularity theorem is assumed.

### 9.1 Contact propagation with a spatially semiconcave subsolution

Suppose u<=v are respectively a continuous G_tau-subsolution and supersolution on a connected open set, u spatially semiconcave with a uniform finite constant on each compact product cylinder. First u is locally Lipschitz in all variables. Spatial supporting slopes p at (x0,t0) are bounded uniformly by evaluating their supporting inequalities at fixed opposite increments. Fix r within the spatial margin and K'=K+1. The scalar function

    h(t)=max_{|y-x0|<=r}[u(y,t)-p.(y-x0)-K'|y-x0|^2/2]

has its maximizers strictly interior for |t-t0|<s, with common s>0, because at t0 the center has boundary deficit r^2/2 and continuity has a uniform time modulus. At a scalar upper test psi, its lifted upper test has zero mixed Hessian, bounded spatial gradient and spatial Hessian K'I. The PDE gives psi''>=-C uniformly. Hence h+C(t-t0)^2/2 is convex and has bounded slopes on a shorter interval. Since u(x0,t)<=h(t) with equality at t0, this bounds u's forward difference. Repeat at base time t to obtain the opposite difference with the same constants. Together with spatial semiconcavity this proves local full Lipschitz continuity of u.

At a contact z0 choose L>Lip(u) and a small r, and set

    v_L(z)=min_{|h|<=r}[v(z+h)+L|h|].

Every competitor is >=u(z)+(L-Lip(u))|h|, so u<=v_L<=v and the contact is retained. Near contact all minimizing shifts have |h|<r/2. Fixed-shift test pullback proves that v_L is still a supersolution; shifting a minimizing competitor by z-z' proves it is locally L-Lipschitz. Moreover v_L(z)=u(z) forces h=0 and hence v(z)=u(z).

Define the smooth flux on full gradients (p,q) by

    a(p,q)=exp((q+|p|^2/2)/tau)(p,1),
    Da=exp((q+|p|^2/2)/tau)/tau
                     * [[tau I+p p^T,p],[p^T,1]].       (9.1)

It is symmetric and positive definite; on every bounded full-gradient ball its ellipticity constants are positive and finite. For a locally Lipschitz subsolution f, full-variable sup convolution f^h remains a subsolution by fixed-translate pullback, is Lipschitz with the same bound, and has D2f^h>=-I/h. At Alexandrov points its PDE gives tr(Da(Df^h)D2f^h)>=0. Mollify at fixed h. The smooth divergences are bounded below by -N Lambda_M/h, and the mollified Hessians converge almost everywhere to the absolutely continuous Alexandrov Hessian (Julin–Juutinen Remark 3.3). One-sided Fatou plus bounded-flux convergence gives div a(Df^h)>=0 distributionally, retaining the favorable singular Hessian sign. At a differentiability point of f, maximizing displacements h b_h are bounded by 2 Lip(f)h. Taylor expansion and comparison with h Df(z) give |b_h-Df(z)|^2=o(1). Therefore Df^h->Df almost everywhere along a countable h sequence, and bounded-gradient dominated convergence passes the flux to f. Supersolutions use inf convolution and the reversed Hessian/Fatou bounds. This proves the needed viscosity-to-weak implications for this explicit flux, rather than importing p-Laplace equivalence for a different equation.

For a locally Lipschitz ordered pair put d=v_L-u. The matrix

    B(z)=integral_0^1 Da(Du+s(Dv_L-Du)) ds

is measurable, symmetric and uniformly elliptic locally; div(B Dd)<=0, d>=0. On any ball about a zero of d solve the linear Dirichlet problem for a weak solution w with w-d in H1_0. Energy tests give 0<=w<=d. Classical solution Harnack and continuity make w identically zero, since w at the center is zero. Then d has zero trace on this ball; its Lipschitz representative vanishes on the sphere. Applying this to every smaller radius makes d zero near the contact. The recovery property of v_L gives v=u there. The original contact set is nonempty, open and closed, hence the entire connected domain. For total dimension two one may use the standard two-dimensional Harnack theorem directly, or lift diag(B,1) and w constantly to three dimensions before applying it. This pays every regularity assumption of the contact argument.

### 9.2 The actual extremal envelope and global contradiction

If C0=0, the exact fits give affine representations on open boxes, whose overlaps and connectedness identify one global affine function. For C0>0, enlarge it to max(C0,1) for growth estimates. The source's shear/scale leaves tau fixed: for

    Vbar(y,s)=[V(x0+R(y+p0 s),t0+Rs)-V(x0,t0)]/R
                       -p0.y-(a0+|p0|^2/2)s,

one has G_tau[Vbar]=R G_tau[V] by test pullback and Delta_y Vbar=R Delta_x V. FIT is unchanged. The equation-free source fit comparisons give centered growth O(K(1+log K)^2), compactness and uniformly subquadratic horizontal tails. The PDE-identification step uses continuity of G_tau, not a homogeneous envelope theorem.

If every horizontal slice is affine, V=P(t).x+c(t). A radius-R fit gives |p-P(t)|<=C0. Adding its estimates at (p ell,ell) and (-p ell,-ell), for R>=ell, bounds

    [P(t+ell)+P(t-ell)-2P(t)].x
       +ell p.[P(t+ell)-P(t-ell)]
       +c(t+ell)+c(t-ell)-2c(t)

uniformly in x. The other terms are bounded since p is, so the coefficient of x vanishes. Thus P is affine in t; centered logarithmic growth forces its time slope to vanish. Tests then give c''=0. This case is affine.

Otherwise a spatial slice has a nonzero Jensen defect; reflection -V(x,-t) makes it positive. Let kappa>0 be the supremum of the finite weighted defect divided by root-mean-square radius. Centering at that radius bounds kappa by the source growth estimate. Normalize approaching configurations to mean zero and second moment one. Centered function compactness, tightness and uniformly subquadratic tails pass their value integrals to a limit and a finite-second-moment measure. The source's geometric barycentric duality admits this measure and gives equality in

    0<=C_s V-V<=kappa^2 s/2.

One fixed normalization creates W=C_t V-kappa^2 t/2<=V with equality at (0,1) and kappa>0. Its spatial Hessian is bounded above by I/t. These are geometric envelope statements; no altered PDE follows from them without the next calculation.

Separate the times in a finite attaining configuration and penalize their deviations from the common mean time. The theorem of sums supplies closed jets of theta_j V; after division by theta_j their inequalities are

    X_j[(q_j,1)]+tau sum_k X_j[(e_k,0)]>=0.

Evaluate the block matrix inequality along ((q_j,1))_j and, separately, along every common horizontal translation ((e_k,0))_j with coefficient tau. First let the theorem-of-sums error go to zero at fixed time penalty, then let the time penalty tend to infinity. Its Hessian vanishes on all these directions. This proves the common-time inequality including precisely tau times the common horizontal trace. Individual time derivatives may be unbounded but do not enter G_tau.

At an upper test phi of W, the lifted test of the weighted sum is

    phi(sum theta_j y_j,t)+kappa^2 t/2
                    +sum theta_j|y_j-sum theta_k y_k|^2/(2t).

The individual directions are q_j=D_xphi+(y_j-x)/t. The variance penalty is affine along these velocities with time speed one, and constant along common horizontal translations. Their weighted mean is D_xphi. The common-time inequality is consequently G_tau[phi]>=0. Thus the actual W is the required subsolution. Section 9.1 gives W=V on all positive times. At fixed t>0 take a global maximizer y* of V(y,t)-|y|^2/(2t); it exists by subquadratic growth. Its supporting inequality, averaged over any configuration of mean y*, gives C_t V(y*,t)<=V(y*,t); the singleton gives equality. But W=V requires C_tV-V=kappa^2t/2>0 everywhere. Contradiction.

This revalidates I236's exact finite-tau rigidity, including its changed-PDE envelope step. It uses no REG_tau assertion, no full-gradient bound for the arbitrary entire solution, and no uniformity as tau tends to zero or infinity.

## 10. Gradient extraction and consequence

The proven power bound for b(s) is for the single full p>=3 family. Reduce gamma if necessary so 0<gamma<=1. At all centers of B1/2^N, D(z)>=1/4. A dimension-only A0 and r0 make lambda=A0 r^gamma good for every 0<r<=r0. On dyadic radii r_j=2^{-j}r0 the inscribed balls have radii rho_j=sqrt(A0)r_j^{1+gamma/2}, and the error is A0 r_j^{1+gamma}.

Evaluate consecutive fits on their common ball to obtain

    |P_j(z)-P_{j+1}(z)|<=C r_j^{gamma/2}.

The slopes converge with this uniform tail. For rho_{j+1}<|h|<=rho_j their Taylor residual divided by |h| is <=C r_j^{gamma/2}<=C'|h|^alpha, where

    alpha=gamma/(2+gamma) in (0,1/3].

Thus U is differentiable everywhere in the half ball with a common Taylor error C|h|^{1+alpha}. Comparing this Taylor estimate at z and z' at the two evaluation points z' and z'+|z-z'|e gives |DU(z)-DU(z')|<=C|z-z'|^alpha, uniformly over unit e; large separations use the original Lipschitz bound. Restrict to b=0, then restore oscillation M. This proves (T).

In particular, if u_p converges locally uniformly in values to an infinity-harmonic v and the local oscillations are uniformly bounded, the gradients converge locally uniformly. The same uniform Taylor error also passes to v: at each fixed center a subsequence of the bounded slopes converges, and the limiting Taylor inequality identifies a unique derivative of v with that error. The two-center Taylor comparison gives v the same alpha bound. Thus this consequence does not require the independently supplied infinity exponent to equal alpha. On nested balls, after normalizing their oscillations, finite differences of length h give

    ||Du_p-Dv|| <= C(h^alpha+delta/h),
    delta=||u_p-v|| on the larger ball.

Choose h=delta^{1/(1+alpha)} for small delta. The bound is C delta^{alpha/(1+alpha)}. For an arbitrary independently given infinity-harmonic comparison function instead of a value limit of this family, use the minimum of the two available exponents; its dimension-two estimate follows by its infinity lift to dimension three. This is a consequence of (T), not a separate nominated theorem; a p-dependent value rate requires its own value-convergence hypotheses.

## 11. Status, risks and contribution boundary

Within the stipulated pinned corpus and the classical interfaces listed in Section 1, the argument completes the unrestricted finite-p target. It is a completed research proof candidate, not an independent gate acceptance. The pivotal new operations are the correct critical-safe lift; continuous elliptic extensions agreeing on constrained test jets; exact projection of both PDE and fits; and the lifted Savin family combined with the repaired quadratic cross-parameter norm transfer. The proof leaves no nonzero-original-gradient or qualitative-flatness hypothesis unpaid.

The first defect found in I344 was the use of an equal-parameter quadratic norm estimate across its different-parameter base/coarse fits. Section 8 repairs it with O(kappa^2 lambda+eta log nu), whose relative error still vanishes. We neither assume nor claim the stronger displayed I344 comparison. Source geometry is reused only after its quantified hypotheses are established, and its PDE-identification step is replaced explicitly.

The exponent is nonexplicit, source truth is stipulated, and literature priority is not demonstrated. Classical Kotschwar–Ni, Uhlenbeck, Savin, weak/viscosity equivalence and linear Harnack are antecedents, not new findings. The result extends the project's quasiconcave/nonzero-original-slope partials; those partials and the actual-gradient consequence are not additional nominations. No count, index, publication or earlier evidence is changed.
