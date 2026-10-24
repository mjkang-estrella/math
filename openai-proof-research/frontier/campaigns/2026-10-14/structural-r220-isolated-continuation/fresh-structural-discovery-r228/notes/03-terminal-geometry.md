# Fixed complex gauge, terminal cone, and the weak continuation

Prefreeze integrated derivations. This is not a frozen theorem or a substantial-contribution claim. All notation and flow-dependent constants are as in 02-concentration.md. The origin p is fixed by the U(10) action; x is a time-dependent momentum coordinate and cannot be substituted for |Z|^2 without the following calculation.

## 1. Affine gauge forced by the flow

Let q=|Z|^2, ell=log q, u the Legendre dual with u_t=K(H), and a(t,x)=u_x-log[x/(1-x)]. Put a0(t)=a(t,0). The source reconstruction is q=x exp(a)/(1-x). Its initial affine choice is allowed; a time-dependent affine correction is not free. The exact K expansion gives

 a0'(t)=132[H_x(t,0)-2H(t,0)].                          (6)

Write G(y)=1+g1 y+g2 y^2+... . The source equation

 Q(D)(G-1)=y^2/2(1/G-1/c),
 Q(D)=(D-1)(D+9)(D+10), d=1/c-1

has Q(2)=132, hence g2=-d/264. Using the weighted estimates for V and V_x at 0 in (6),

 a0'(t)=-d/(2rho^2)+O(rho^(-2+delta))+O(rho^-1).

Since dt=-2rho d rho, the error is integrable after subtracting d log rho. There is a finite real a_* with

 a0(t)=d log rho+a_*+O(rho^delta).                      (7)

This drifting affine term is responsible for the physical coordinate scale. It is not an additional geometric parameter selected by the certificate.

## 2. Exact integral reconstruction and the exterior limit

For x in a fixed small interval [0,x0], v and xG(x/rho) are bounded above and below by positive multiples of x. Expanding v gives

 v=xG+x^2(1-2G)+x^3(G-1)+x^2(1-x)^2 V.

Therefore

 |1/v-1/[xG(x/rho)]|<=C[1+(x+rho)^(-1+delta)].           (8)

Set

 I(Y)=integral_0^Y (1/G(s)-1) ds/s,
 J(t,x)=integral_0^x {1/v(t,s)-1/[sG(s/rho)]}ds.

The singularities in these definitions are removable/integrable. The exact identity is

 ell(t,x)=log x+a0(t)+I(x/rho)+J(t,x).                 (9)

The all-order source tail gives

 I(Y)=d log Y+kappa+O(Y^-2) as Y tends to infinity.

Here kappa is a fixed real number determined by the supplied G. On every annulus x>=epsilon>0, the X estimate, its temporal Holder control, and the equation give a terminal V0 and local spatial regularity; the ordinary uniformly parabolic interior bootstrap gives higher derivatives on smaller annuli. At the divisor, the source smooth invariant endpoint chart is used. In (8), 1+s^(-1+delta) is an integrable dominating function. Thus J(t,x) tends to J0(x), with |J0(x)|<=Cx^delta. Equations (7)-(9) give

 ell0(x)=(1/c)log x+B+J0(x), B=a_*+kappa.               (10)

In particular momentum collars shrink to the fixed point p in the fixed complex chart. Their radius is O(x^(1/(2c))) at the terminal time. Uniformly for sufficiently small rho the same localization follows by splitting x<=rho and x>=rho in (9). This supplies the localization missing from a momentum-only concentration statement.

The terminal profile satisfies

 v0(x)=cx[1+O(x^delta)],
 q=e^B x^(1/c)[1+O(x^delta)],
 x=L q^c[1+O(q^(c delta))], L=e^(-cB)>0.              (11)

The differentiated versions needed up to second spatial order follow from the corresponding weighted V jets and (8). For the terminal potential, dPhi0/dlog q=x, hence

 Phi0(q)-Phi0(0)=(L/c)q^c[1+O(q^(c delta))].           (12)

This concerns an actual global potential limit, not only a formal profile: the global fixed-gauge equation Phi_t=S-110 and |S|<=C/rho imply uniform C0 convergence at rate O(rho). Thus omega0=omega_FS+i ddbar phi0 is a positive closed current in the SAME FS class; it is smooth and positive away from p, with the original smooth divisor endpoint. Bounded omega_FS-psh potentials have full Monge-Ampere mass. Here this can also be checked directly: the radial mass of a collar x<=epsilon is proportional to epsilon^10, so there is no missing point mass.

As 1/2<c<1 follows from the certified d rectangle, (12) implies exactly C^(1,2c-1) spatial regularity at p and failure of C^(1,beta) for beta>2c-1. More explicitly |grad Phi0|<=C r^(2c-1), |Hess Phi0|<=C r^(2c-2) for r=|Z|>0; a near/far pair argument gives the asserted Holder exponent. On any radial line its leading derivative is 2L r^(2c-1), which rules out every larger exponent. The Hessian is unbounded, so this limit is outside the bounded-complex-Hessian small-data hypothesis of He-Zeng. No assertion about a second-order maximum principle is used.

## 3. Physical cone and rescaled core

Take the physical real metric convention g_R=2 Re(g_{i bar j} dz_i dbar z_j). On S^(2n-1) let eta be the unit Hopf form and g_H the horizontal round metric, so g_round=eta^2+g_H. Directly from the radial complex Hessian,

 g_R=dx^2/(2v)+2v eta^2+2x g_H.                       (13)

For example, when v=x this is the Euclidean metric in radius sqrt(2x), checking all factors. With R=sqrt(2x/c), (11) turns (13) into

 g0=dR^2+R^2(c g_H+c^2 eta^2)+O(R^(2delta))

in relative coefficients. The metric completion adds one point; its unique tangent cone has link (S^19,c g_H+c^2 eta^2). Its volume density relative to Euclidean R^20 is c^10: the 18 horizontal directions contribute c^9 and the Hopf direction c. The radial distance to x=epsilon is O(sqrt(epsilon)), uniformly along the smooth flow because v is comparable to x near 0. Together with local smooth convergence off p, this gives metric-space convergence to that completion, rather than merely convergence on a moving chart. This is a direct radial estimate, not a general compactness theorem used without hypotheses.

Define QG(y)=y exp(I(y)), so QG'(y)/QG(y)=1/[yG(y)]>0, QG~y at 0 and QG~exp(kappa)y^(1/c) at infinity. At x=rho y, (7)-(9) imply

 q=e^(a_*) rho^(1/c) QG(y)[1+O(rho^delta)]

on compact y intervals, with the corresponding finite derivative estimates. Thus under Z=e^(a_*/2)rho^(1/(2c))zeta and metric multiplication by rho^-1, the limit potential is

 Psi(|zeta|^2)=integral_0^{Y(|zeta|^2)} ds/G(s),
 Y=QG^(-1).

Indeed dPsi/dlog|zeta|^2=Y. Its profile is v=Y G(Y), smooth at the origin, positive, and complete at infinity since integral^infinity dY/sqrt(2YG(Y)) diverges. Its cone at infinity is exactly the terminal cone above. This is the supplied shrinking model expressed in the correct physical complex gauge; it is not a new soliton.

More generally put t=lambda^2 s and Z=e^(a_*/2)lambda^(1/(2c))zeta, multiply metrics by lambda^-1, and keep s in a compact subset of (-infinity,0). The limiting momentum is sqrt(-s)Y(|zeta|^2/(-s)^(1/(2c))). The time scaling is lambda^2, as required for Calabi flow under metric multiplication. The weighted correction tends to zero; local fourth-order regularity upgrades the finite-jet convergence on compact space-time sets. No forward-time solution follows from this backward-time limit.

## 4. Execute the classical weak continuation

The global C0 convergence above already places phi0 in the finite-energy E2 space, with a definite AM normalization after subtracting the common smooth normalization constant. The smooth curve has bounded Mabuchi speed near 0: its speed is the evolving L2 norm of S-110, bounded by the p=2 estimate (also by Calabi-energy monotonicity). Its d2 length on [-epsilon,0) is O(epsilon). Hence it has a d2 limit. This is phi0, not a second unknown limit: the straight segment between any two smooth phi(t_i), phi(t_j) gives d2<=sqrt(Vol)||phi(t_i)-phi(t_j)||infinity, because all segment Monge-Ampere masses equal Vol. Passing to the completion identifies its limit with the same bounded potential phi0. This uses the actual smooth approximating sequence, rather than assuming a new regularization of the cusp.

The actual Berman-Darvas-Lu Section 6 proof identifies smooth Calabi flow with the EVI gradient flow by integrating the K-energy slope inequality along the smooth curve, then approximating a general E2 comparison point by smooth points. The EVI is

 1/2[d2(c_t1,v)^2-d2(c_t0,v)^2]
 <= (t1-t0)K(v)-integral_t0^t1 K(c_t)dt.

The established E2 semigroup extends through phi0, so the original smooth trajectory has a unique weak continuation. Since this class contains FS, the weak-flow convergence-to-a-minimizer results apply at their stated topology. This is a fully available classical continuation, credited in full, and is not proposed as a new consequence of substance. The read proof does NOT assert immediate smoothness from this cusp, and the C0/d2 estimate is not a curvature estimate.

The classical reduction also supplies symmetry and controlled metric-space approximation. For each A in U(10), pullback acts isometrically on d2 and preserves K-energy and the initial phi0. Pulling back the EVI trajectory therefore gives the same trajectory by uniqueness. The forward weak flow is U(10)-invariant. Contractivity gives, for the EVI semigroup T_s and any t_j up to0,

 d2(T_s phi(t_j),T_s phi0)<=d2(phi(t_j),phi0) ->0

uniformly for all s>=0. These are global WEAK approximating trajectories; the smooth trajectory starting at phi(t_j) is only known until its own finite singular time, so this is not a supply of smooth approximants on a common positive interval.

The terminal scalar S0 on the punctured manifold has finite L2(dmu0), and the Calabi energies of the backward flow converge to its value. This follows from local convergence at each x>0, |S|<=C/(x+rho)<=C/x, and domination by x^7 dx in dimension10. There is no scalar-energy atom at p. The metric slope of the lower semicontinuous convex K-energy at phi0 is at most the liminf of the smooth slopes, hence finite. The EVI continuation has bounded metric speed near0 and nonincreasing slope. This is genuine additional control already furnished by the classical convex-flow reduction; it is not a smooth-curvature estimate or a proof of an expanding metric profile.

Nor does the compact E2 construction automatically give a smooth self-similar flow on C^10. Its finite-volume completion and compact K-energy must first be replaced by a legitimate noncompact framework, or a smooth rescaled compactness theorem must be proved. The pointed inner limits available on negative times do not provide that positive-time compactness.

To identify a forward expanding profile with that weak continuation one must construct an actual compact forward solution with finite-energy convergence to phi0 and verify the EVI/flow identification. A formal positive flat expander, if obtained, still leaves this compact singular-initial-data problem. Its analysis is continued in 04-forward-construction.md; no smooth continuation across t=0 (which is impossible for the original maximal smooth flow) is asserted.
