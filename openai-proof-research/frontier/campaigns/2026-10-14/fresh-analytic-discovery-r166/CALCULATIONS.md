# SOURCE366: feasibility calculations, before any freeze

PREFREEZE. Codex / GPT-6 Astra / high / default service tier. No theorem, independent grade, acceptance or count is asserted. The source theorem and all its operative proofs at the stipulated pin are accepted. The exact canonical objects were read in full before these calculations. The 2025 DF book's entire crack-tip Chapter 5 and operative weak-L4 proof were read, together with the current Deangelis v2 interaction proof and the relevant original I122 section. This is a distinct endpoint-asymptotic investigation, not a retry of I122's polynomial graph-count target.

## 1. Reductions already paid

SOURCE366 gives local boundedness, SBV extension, removal of excess crack length, all interior model neighborhoods, discrete endpoints/triods, and local weak L4. Its finite translation interaction, independent one-sided jump tests, and harmonic continuation exclude isolated compact pieces in generalized whole-plane limits. Deangelis v2 also pays the optimized two-translation/Hodge alternative. Compact chart covers and weaker Sobolev estimates are not candidates.

DF's actual endpoint proof supplies more than the displayed geometry: on the punctured tip chart the crack is locally C1,1, u solves the Neumann equation, and the auxiliary Poisson correction converts its bounded fidelity forcing to a harmonic-conjugate problem with explicit rapidly decreasing boundary errors. Its homogeneous case has vanishing tip curvature. Its stated bounded-measurable-fidelity conclusion is C1,alpha, not a blanket C2 assertion. We retain this distinction, including the fact that measurable g need not give continuous curvature away from the tip.

## 2. Exact endpoint coordinates and the prospective stronger operation

At a loose end translated to zero, set r=exp(-t), gamma(r)=r(cos theta(t),sin theta(t)), a=theta'. Normalize the value u(0) to zero, shifting g by the same constant; a local finite bound still holds. Let w be the DF corrected harmonic conjugate and

 f(phi,t)=r^(-1/2) w(r,phi+theta(t)),
 S(phi)=sqrt(2/pi) sin(phi/2), c=S'(0)=1/sqrt(2*pi).

All derivatives below are a.e. or distributional when g is only bounded. The paid first decay gives small, exponentially decreasing C1 errors on fixed-width strips and H2 strip bounds, with a positive but unspecified exponent. The actual forced equations are

 L f=(a'-a) f_phi+2a f_tphi-a^2 f_phiphi,
 L=partial_tt-partial_t+partial_phiphi+1/4,
 f(0,t)=f(2pi,t)=H1(t),
 (a'-a-a^3)/(1+a^2)^(5/2)=f_phi(2pi,t)^2-f_phi(0,t)^2+H2(t).

For each s<3/2, the paid correction estimates give |H1|+|H1'|+|H2| <= C_s exp(-s t), with H1 in the stated local C1,1-epsilon and H3/2 trace classes. No derivative of H2 is available or assumed.

The prospective full operation is a leading odd spectral expansion for EVERY such bounded-data endpoint, including the zero-leading-coefficient case. Let nu2 be the first positive root above 1/2 of

 nu cos(pi nu)=(pi/2)(1/4-nu^2) sin(pi nu),

and mu=nu2-1/2 in (1,3/2). The question is whether, after rotating to the tangent and orienting the crack outward, there is A in R with

 a(t)=A exp(-mu t)+o(exp(-mu t)),
 a'(t)=-mu A exp(-mu t)+o(exp(-mu t)) in the essential-supremum sense.

This would yield theta(t)=-(A/mu)exp(-mu t)+o(exp(-mu t)) and

 kappa(r)=(1+mu) A r^(mu-1)+o(r^(mu-1)),

up to the selected curvature orientation. It includes A=0 without asserting a nonzero first mode. It is not frozen: the required forced infinite-mode estimate has not yet been proved. A pointwise C2 assertion for rough fidelity would be stronger and is not silently substituted.

## 3. Exact parity reduction: slow even errors are coefficients, not additive forcing

Use reflection phi -> 2pi-phi. Write f=E+O, where E=S+e is even and O is odd. The exact equations become

 L O=(a'-a)(S_phi+e_phi)+2a e_tphi-a^2 O_phiphi,        (P1)
 L e=(a'-a)O_phi+2a O_tphi-a^2(S_phiphi+e_phiphi).       (P2)

The boundary conditions are O(0,t)=O(2pi,t)=0 and e(0,t)=e(2pi,t)=H1(t). In particular H1 has no direct odd boundary part. Since E_phi(2pi)=-E_phi(0) and O_phi(2pi)=O_phi(0), the exact jump of squares is

 f_phi(2pi)^2-f_phi(0)^2=-4E_phi(0) O_phi(0).

Thus

 a'-a=-4c O_phi(0)+N,
 N=a^3-4[(1+a^2)^(5/2)E_phi(0)-c]O_phi(0)
       +(1+a^2)^(5/2)H2.                              (P3)

This calculation removes a false obstruction: an even error with a slow exponent does not create its square as an independent odd forcing. It multiplies O or a. On a fixed strip where the paid C1 norms of e,O and a are small,

 ||N||_Lp <= C (||e||_C1+||a||_infty^2)
                  (||O_phi(0,.)||_Lp+||a||_Lp)
             + C ||H2||_Lp.

Likewise the bulk residual R=LO-(a'-a)S_phi satisfies

 ||R||_L2 <= C ||e||_C1 ||a'-a||_L2
          +2 ||a||_infty ||e_tphi||_L2
          +||a||_infty^2 ||O_phiphi||_L2.

For the middle term one can use the paid decay of ||e||_H2 on a strip times ||a||_infty. These are explicit local product bounds; they do not by themselves supply a weighted inverse on the infinite cylinder.

## 4. The nonlinear moment condition retains the same parity advantage

Let b=f/2-f_t+a f_phi. The truncated inner variation identity for w says

 B(f,a):=integral_0^(2pi) [(b^2-f_phi^2) sin phi
                         -2 b f_phi(1-cos phi)] dphi = T(t),

where the actual DF Poisson-correction and fidelity terms give |T(t)|<=C_s exp(-s t), s<3/2. They use only bounded g, the square-root estimate for u and grad u, and grad u_aux(0)=0. This is not an assertion that g has a classical trace: DF's bounded variational representative g_K is the input.

Set b_e=E/2-E_t+a O_phi and b_o=O/2-O_t+a E_phi. Parity gives the EXACT identity

 B=2 integral (b_e b_o-E_phi O_phi) sin phi
     -2 integral (b_e O_phi+b_o E_phi)(1-cos phi).

For O=a=0 the entire expression vanishes for every even E, even when E depends on t. Linearizing at (E,O,a)=(S,0,0), the terms in O and O_t cancel except for

 -2 sqrt(2/pi) integral O_phi sin(phi/2) dphi.

The linear a term also cancels. Consequently the moment defect is bounded by

 |integral O_phi sin(phi/2)|
 <= C (||e||_C1+||O||_C1+|a|)(||O||_C1+|a|)
       +C_s exp(-s t).                                 (P4)

The exact algebra, rather than an unsupported statement of 'quadratic error', is essential: an even-only error produces no moment defect. This pays the leading compatibility calculation needed to try a sharp odd estimate with rough fidelity.

## 5. What the homogeneous spectral result actually pays

The DF odd operator uses zeta=O-theta*c*cos(phi/2). Its spatial boundary condition is Ventsel, not Dirichlet. It has a two-dimensional Jordan sector generated by cos(phi/2) and (phi-pi)sin(phi/2), and the higher modes

 zeta_k(phi)=c_k sin(nu_k(phi-pi)), k>=2,
 mu_k=nu_k-1/2>1.

For homogeneous compatible solutions, the moment condition eliminates the generalized Jordan mode and decay removes the growing branches exp((1+mu_k)t). The surviving coefficients are exp(-mu_k t). The eigenvalue equation puts nu2 between 3/2 and 2, so mu2 lies strictly between 1 and 3/2. This is the reason the bounded-fidelity error rate 3/2-minus is potentially sufficient.

Simply applying the homogeneous theorem to (P1)-(P4) is invalid: N is only bounded/measurable; the spatial forcing naturally has L2 regularity; the moment constraint is inhomogeneous; and the even boundary lift is not C2. A cutoff or formal termwise differentiation cannot erase those facts.

## 6. A workable forced-state realization found before freeze

The dangerous formal step is to replace the dynamic endpoint condition by a spatial Ventsel condition involving the boundary value of the L2 bulk error. That boundary value need not exist. Retain it instead as an independent coordinate.

On 0<phi<pi define H=L2(0,pi) plus R, with positive norm ||z||_L2^2+(pi/2)|z_b|^2, but use the nondegenerate indefinite pairing

 [z,h]=integral z h -(pi/2) z_b h_b.

The domain of A consists of (z,z(0)) with z in H2(0,pi), z(pi)=0, and

 A(z,z(0))=(z''+z/4, -(2/pi)z'(0)).

Green's formula makes A symmetric for [.,.]. The state Z=(zeta,zeta(0)) satisfies the exact equation

 Z_tt-Z_t+A Z=(R,-cN).                                (F)

In particular the only boundary forcing is N, which is L-infinity; there is no derivative of N and no value R(0). This resolves the immediate trace obstruction.

The two Jordan vectors are e1=(cos(phi/2),1) and e0=((phi-pi)sin(phi/2),0), with A e1=0 and A e0=e1. The higher eigenvalues are -lambda_k=-(nu_k^2-1/4). After normalizing the eigenfunctions in the positive pairing on their span, their endpoint coordinates are O(1/k), their L2 norms are bounded above/below, and the high modes form a Riesz basis of a closed positive subspace of H. The paid H1 completeness, density of the trace graph in H, and Green orthogonality give a direct-sum completion by the two Jordan vectors. This completion, rather than an unsupported use of the H1 expansion for arbitrary L2 forcing, is the proposed new analytic bridge.

For each high coefficient y_k, (F) is

 y_k''-y_k'-lambda_k y_k=F_k,
 lambda_k=mu_k(mu_k+1).

The full-line Green kernel is

 G_k(s)=-(2mu_k+1)^(-1) exp(-mu_k s) for s>=0,
 G_k(s)=-(2mu_k+1)^(-1) exp((mu_k+1)s) for s<0.

Its derivative jump is one. The two Jordan coefficients satisfy scalar y''-y'=forcing, triangularly coupled. Their decaying solution is the future integral integral_t^infinity (1-exp(t-s))forcing(s) ds. Thus the already-paid coarse decay excludes all homogeneous center/growing solutions; the nonlinear moment identity was needed to obtain that coarse decay, but need not be differentiated a second time.

On fixed-width strips let X control ||O||_H2+||theta||_H2 (after subtracting the limiting angle) and let epsilon>0 be a paid coarse exponent. The parity equations imply

 ||(R,N)||_L2(strip_t) <= C exp(-epsilon t) X(t)+C_s exp(-s t), s<3/2.

Starting with X(t)<=C exp(-epsilon t), the Green estimate increases the exponent by a fixed positive increment until it is arbitrarily close to mu2. Then the forcing decays strictly faster than mu2. The lowest stable coefficient therefore has a limit after multiplication by exp(mu2 t), while all higher modes and the Jordan sector are smaller. This route uses successive known decay bounds, avoiding the circular assumption that an unproved faster weighted norm is finite.

The remaining feasibility check is the full graph-norm and trace upgrade of this state-space construction. If it closes, the exact little-o curvature expansion in Section 2 is viable; neither homogeneous curvature regularity nor a bare compact-cover corollary would be the proposed operation.
