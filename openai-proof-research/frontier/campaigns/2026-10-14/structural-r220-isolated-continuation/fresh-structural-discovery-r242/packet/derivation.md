# Source367: integrated quantitative instability calculation — PREFREEZE

This is supporting research, not a frozen nominee. No correctness, contribution, acceptance or count is assigned. Runtime: Codex / GPT-6 Astra / xhigh / ultrafast, verified from live inherited options. The source at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, including its full finite-certificate operations, is stipulated true.

## Exact problem and the compatible class

For an open D in R^n, J(u;B)=integral_B (|grad u|^2+1_{u>0}) dx, with volume coefficient exactly1. A local minimizer is nonnegative u in H^1_loc(D), compared on every ball B compactly contained in D against every nonnegative v in H^1(B) with v-u in H^1_0(B). Global means D=R^n. It does not mean minimizing only over cones. Work with the locally Lipschitz representative. The free boundary is D intersect boundary{u>0}; a regular point has a halfspace blowup (x.e)_+, |e|=1; a singular point has none. The source proves d_*=7 for such minimizing cones, smoothness through6, and the stated sharp singular-set bounds. Those results and their product/dimension-reduction consequences are paid.

The calculation below concerns a different, explicitly weaker class: a smooth connected proper spherical domain Omega in S^5 with compact smooth closure and nonempty boundary, carrying g>0 solving Delta_S g=-5g, g=0 and grad_S g=N on the boundary. Its homogeneous extension U(r theta)=r g(theta), extended by zero outside the cone, is a classical one-phase critical cone. Assume T=Hess_S g+g Id is not identically zero. No minimizing or stability assumption is imposed. Such a cone cannot be minimizing by Source367; it is not a minimal hypersurface cone. A global representative with one-sided regular cone boundary is intended. Nonempty examples are constructed below.

For this class, the source's local identities require only the displayed equations: p=grad g, w=|T|, B=nabla T, Delta T=5T, Delta(g^2+|p|^2)=2w^2, and H=-T(N,N). The maximum principle and Hopf lemma give g^2+|p|^2<1 inside, H>0 and w>=H>0 on the boundary. Thus A=T/w and X=B/w have exactly the certificate's trace-free symmetries where w>0. This establishes the interface; no stability of critical points is inferred from stationarity.

## The full paid remainder, not just the proposition headline

Let a=29/50, f,U,K,M,P be the exact Source367 polynomials, C_lijk=K_lijk-K_iljk and G_lijk=delta_li U_jk+C_lijk. Define

h=w^a sqrt(f),  Z_l=w^(2a)(G_lijk X_ijk+w M_l+P_l).

Here the geometric certificate parameter is z=1. Let ell_*=grad h/h on {w>0}. The source's coefficient proof gives

I >= c_w w^2+c_z z^2+c_l |ell|^2+c_X |X|^2,

with c_w=673/18400, c_z=438907/12000000, c_l=2844869/24900000 and c_X=3479389/7600000. The skew-fourth-derivative and Laplacian contractions, followed by square completion at ell_*, therefore give

div Z >= |grad h|^2+4h^2+c_z w^(2a)+c_w w^(2a+2)
             +c_X w^(2a-2)|B|^2+c_l |grad h|^2/f.             (1)

The boundary reflection operation kills the uncontrolled even-normal third jets; with the inward normal it gives

N.Z+Hh^2 >= delta w^(2a+1),   delta=6984137359/31250000000.  (2)

These are consequences of actual proof operations, not an independent certificate or a new numerical result. A repeated tangential eigenvalue or lambda=-H/w tending to0 does not destroy the polynomial boundary margin; that margin persists at lambda=0 in the source. The algebraic parameter w can tend to0, so these coefficient inequalities alone do not bound the geometric mass integral w^(2a) below or identify it with a distance or energy gap. No sequence of admissible nonflat cones with that mass tending to0 has been constructed or asserted here.

## Removing Hessian zeros with enough convergence to retain the terms

Because w>0 on the compact boundary, its zeros lie in an interior compact set. The source's regularized Bochner calculation, with W_e=w^2+e and an interior cutoff chi covering that zero set, yields

(4a-2) integral chi W_e^(a-1)|B|^2 <= a^(-1) integral (Delta chi)W_e^a.

Since4a-2=8/25>0, monotone convergence gives J_B=integral_{w>0} w^(2a-2)|B|^2<infinity. Also I=integral w^(2a) and K=integral w^(2a+2) are finite, and I>0.

Set alpha_j=vartheta(jw), where vartheta=0 on[0,1], =1 on[2,infinity), and v_j=alpha_j h, extended by0 at w=0. These functions are smooth on the closure. Uniform coefficient bounds give |grad h|^2 <= C(w^(2a)+w^(2a+2)+w^(2a-2)|B|^2). Moreover

integral h^2|grad alpha_j|^2 <= C integral_{0<w<2/j} w^(2a-2)|B|^2 ->0.

Thus v_j converges strongly in H^1 to a function h extended by0 on the zero set; its weak derivative agrees with grad h off that set and is0 there. Boundary traces equal h for all sufficiently large j, since min_boundary w>0. The mixed flux cutoff term is bounded by an integrable multiple of I+K+J_B and supported where0<w<2/j, hence tends to0. This is the necessary all-term convergence, not an assertion that the Hessian-zero set is harmless by dimension. It also shows why the cutoff index j need not be uniform over cones.

Multiply(1) by alpha_j^2, integrate and use(2); after the preceding convergence, one obtains

E+4M-B_H <= -c_z I-c_w K-c_X J_B-c_l integral |grad h|^2/f-delta S,  (3)

where E=integral_Omega |grad h|^2, M=integral_Omega h^2, B_H=integral_boundary Hh^2, and S=integral_boundary w^(2a+1). In particular M>0. No use of a stability inequality was made in(3).

## Uniform form gap and an explicit nonsharp constant

Let F0 be the sum of absolute values of the34 integer f-coefficients in TableI, divided by250000. Every scalar f-monomial has magnitude<=1 on |A|=1, tr A=0, g^2+|p|^2<=1: each p.A^k.p is bounded by |p|^2||A||op^k<=1, as are powers of g and tr A^3. Consequently0<c_z<=f<=F0, uniformly. A small rational calculation, recorded separately, gives the exact F0 and constants below; it does not replay upstream verification.

Since M<=F0 I and B_H<=F0 S (H<=w), (3) implies

Q_S(h):=E+4M-B_H <= -sigma(E+M+B_H),

sigma=min(c_z,c_l,delta)/F0=c_z/F0>0.                    (4)

This is a relative quadratic-form gap, stronger than merely an L^2 Rayleigh gap. It is justified by the full remainder and the boundary term. In particular the lowest Robin Rayleigh value for integral|grad v|^2-integral H v^2 is at most -4-sigma. The weak test h is legitimate; smooth v_j preserve any slightly smaller strict margin. This is an explicit application of the paid inequalities, not evidence of a distinct substantial contribution.

## Logarithmic annuli and Morse index

For t=log r, let phi(r,theta)=r^(-2) psi(t)h(theta), with psi compactly supported in an interval I_t of lengthL. Denote A0=integral psi^2 and A1=integral |psi'|^2. Direct polar integration in R^6 gives

Q_C(phi)=integral_C |grad phi|^2-integral_boundaryC H_E phi^2
        =A0 Q_S(h)+M A1,                                  (5)

because H_E=H/r, the radial Hardy constant is4, and integral psi psi'=0. Also the positive comparison norm is

N_C(phi)=integral_C (|grad phi|^2+r^(-2)phi^2)+integral_boundaryC H_E phi^2
        =A0(E+5M+B_H)+M A1.                               (6)

Choose L to satisfy pi^2/L^2<sigma/2. The sine on that interval has A1/A0=pi^2/L^2. It lies in H^1_0; approximate it and h by smooth compactly supported admissible tests. Equations(4)-(6), first for the limiting test, yield

Q_C(phi) <= -(sigma/2) A0(E+M+B_H)
           <= -tau N_C(phi),   tau=sigma/(10+sigma).        (7)

A harmless further margin makes this a smooth test. On any annulus r0<|x|<r1, each disjoint logarithmic interval of the chosen length supports one negative direction. Hence its Dirichlet radial / free Robin-side Morse index is at least floor(log(r1/r0)/L). The statement uses the quadratic form on the cone, not a claim that arbitrary nearby solutions have the same free boundary. For a classical Bernoulli cone the second-variation collar construction in Source367, or the Jerison--Savin operation, realizes each smooth negative direction by a compactly supported admissible deformation. The allowed amplitude can depend on the cone and support.

## Precisely what linear perturbations this controls

Suppose a pulled-back symmetric quadratic form Q_tilde on the same annulus has

|Q_tilde(v)-Q_C(v)| <= epsilon N_C(v)

for all tests there, with epsilon<tau/2. Equations(7) and smooth approximation preserve each negative direction and the disjoint-support index count for local forms. This is a genuine nonempty class of linear operators: take gradient coefficient I+A(x) with symmetric ||A||op<=epsilon, inverse-square potential V(x)/r^2 with |V|<=epsilon, and boundary coefficient (1+b(x))H_E with |b|<=epsilon. Arbitrary measurable such coefficients give the form bound by direct integration; choosing one nonconstant bounded A supplies a nontrivial example. This does not assert that these three coefficients are the compatible second variation of a new nonlinear Bernoulli minimizer.

A C^2 deformation of a fixed smooth cone gives some small form perturbation on a fixed compact annulus, with constants depending on that cone's charts, curvature and trace constants. The relative gap alone does not supply those geometric constants uniformly. In particular an additive curvature error is not a relative H_E error where H_E is small. Passing from a uniformly close function to such control of its free boundary requires a separate regularity theorem with the correct hypotheses.

## Nonvacuous smooth critical cone in dimension6

Write x=(y,z) in R^5 x R, rho=|y|, s=z/rho. Put b=sqrt(2sqrt(3)-3), P(s)=1-2s^2-s^4/3, and

U(y,z)=c rho P(z/rho) on |z|<b rho, and0 otherwise,
c=[4b(1+b^2/3)sqrt(1+b^2)]^(-1).

The function P is positive on(-b,b), vanishes at±b, and solves

(1+s^2)P''-4sP'+4P=0.

This identity is exactly rho Delta_R6(rho P(z/rho))=0. At s=±b, |grad(rho P)|=|P'(b)|sqrt(1+b^2), so the chosen c gives |grad U|=1. It is one-homogeneous and globally Lipschitz; its spherical band is |t|<arctan b. The two conical boundary sheets are smooth away from0, with positive phase on one side. The origin has no role in the compact annular variations. The boundary first variation vanishes because the Bernoulli slope is1; integration over an excised ball contributes O(r^5), which vanishes, so the extension is stationary globally as well. It is nonflat. Its absence from the minimizing class is supplied by the paid source theorem, not by calling a stationary cone a minimizer.

For an independent transparent angular instability check on this particular example, set v(t)=cos(t)^(-4). The spherical Laplacian on zonal functions is v''-4tan(t)v', so Delta_S v=4sec(t)^2 v. At either side, inward normal differentiation gives partial_N v=-4b v, while H=4b. Thus v satisfies the Robin boundary condition. Integration by parts yields

integral |grad v|^2-integral H v^2+4 integral v^2
       =-4 integral tan(t)^2 v^2<0.

This example verifies that the class and the radial-instability construction are nonempty. It does not constitute a new minimizing example, and no cone gluing is performed.

## Remaining nonlinear operation

A finite positive certificate margin is now genuinely connected to a uniform relative Robin-form gap and a logarithmic annulus length, by(1)-(7). What remains unpaid for a stronger Bernoulli conclusion is uniform nonlinear geometric control: construct compatible perturbed critical/minimizing objects, transfer their complete second variation with uniform constants, and retain a finite admissible deformation size or a quantitative singularity scale. The source does not give a universal collar, bound curvature derivatives, control the cutoff index, or identify the form perturbations with the second variation of an arbitrary variable-coefficient energy. No uniform singular-point count, singular-set packing theorem, nonlinear isolation modulus, or singular-cone asymptotic rate is claimed here.

The most direct Euclidean z=0 route is already present in the actually read r99 original section, including all four diagonal slacks, third-derivative absorption, Hessian-zero removal and the exponent79/25. It is not being reopened as a nominee. Jerison--Savin already provide the angular Robin/radial-ODE instability operation. Their pointwise strictness is not by itself a uniform gap; here the stronger bound comes from the paid Source367 remainder. There is no identified additional nonroutine operation warranting a freeze.

Exact arithmetic: F0=188476004/15625, sigma=438907/144749571072. One explicit integer logarithmic interval length is L=3633, since L^2 sigma>=40 and pi^2<10. The numerical length is not optimized.


## An all-scale asymptotic consequence, with its topology stated

The form calculation can be transported to an actual classical one-phase solution only after the required interface is supplied. Here is the precise sufficient condition and its complete use, recorded as a supporting implication rather than a new nominee.

Fix the preceding nonflat smooth cone U in R^6 and L=3633. Let u be a classical Bernoulli solution on a punctured neighborhood of0. Suppose that for every sufficiently small r there is a C^2 diffeomorphism F_r from the closure of the cone's positive phase in A={1<|x|<exp(L)} to the positive phase of u_r(x)=u(rx)/r in the corresponding annular neighborhood, mapping the side free boundary to the side free boundary, and with F_r->Id in C^2 on that compact regular annulus. Assume the identification is on a neighborhood of the support of the test, so artificial radial caps impose zero trace and do not generate boundary terms. Require convergence of the pulled-back Bernoulli curvature coefficients as furnished by that C^2 boundary convergence. This is a statement about smooth regular closures away from the cone vertex, not about normal graphs only on an incomplete subset of a singular link.

On this fixed annulus H_E has a positive minimum by compactness and Hopf strictness. The pulled-back Dirichlet matrix det(DF_r) DF_r^(-1)DF_r^(-T) tends uniformly to I. The pulled-back side coefficient H_{u_r}(F_r(x)) J_boundary(F_r) tends uniformly to H_E(x), and hence relatively uniformly because min H_E>0. Thus, for any prescribed epsilon>0, all sufficiently small r satisfy

|Q_{u_r}(v composed with F_r^(-1))-Q_U(v)| <= epsilon N_U(v).

Take epsilon<tau/2. Equation(7) yields a negative second-variation test on every annulus r<|x|<r exp(L) after identification, with slightly shrunken radial supports if necessary. For disjointness without assuming F_r preserves the radial variable, use logarithmic cells of length L+2: place the test in the middle interval of lengthL and use C^0 closeness of F_r so its support lies within that cell. For all r below one common r_*, the margin1 at each end suffices. Packing these cells shows

index_u({rho<|x|<r_*}) >= floor(log(r_*/rho)/(L+2))

up to omitting at most one outer cell to ensure the common threshold. Equivalently choose r_* one cell below the threshold, in which case the stated floor bound holds exactly. In particular the index near0 is infinite. Scaling preserves the sign of the form: in dimension6 it multiplies by r^4 for an unscaled test amplitude. The analogous exterior statement follows for all sufficiently large r, with index growing at least linearly in logarithmic radius. The cone itself satisfies the assumption, so it is nonvacuous.

If the convergence is known only along a sequence, there is no such uniform logarithmic density conclusion. Nevertheless a subsequence of sufficiently separated scales gives infinitely many disjoint negative tests, provided the same fixed-annulus C^2 convergence holds on that subsequence. Mere H^1 or locally uniform convergence does not supply the curvature or form interface. No rate of convergence, uniqueness of tangent cones, or existence of new asymptotically conical solutions is inferred.

This consequence uses the classical persistence of a strictly negative quadratic-form direction; Jerison--Savin already supply the cone/radial instability mechanism. It does not close the quantitative nonlinear-isolation problem.


## The actual finite-amplitude competitor, and why its size is not uniform

Fix one cone, one smooth negative annular test phi and Q_C(phi)=-q<0. On a collar of the compact side-boundary support, extend U smoothly across its zero surface as F with the same jets. Choose the collar so |grad F| is bounded away from0, F has the prescribed sign on either side, and the affected positive-phase interior outside the collar has a positive lower bound wherever phi is nonzero. For sufficiently small |epsilon|, use (F+epsilon phi)_+ in the collar, U+epsilon phi in the remaining positive support, and U elsewhere. This is nonnegative, lies in H^1, and has the same trace as U on any containing ball.

In the coordinate xi=F, the moving edge is b_epsilon=-epsilon phi_0+epsilon^2 phi_0 phi_N+O(epsilon^3). The volume Jacobian has j(0)=1 and j'(0)=2H_E, while partial_xi |grad F|^2=-2H_E. The fixed-domain cross term is -2epsilon integral_boundary phi. The signed layer integral contributes 2epsilon integral_boundary phi-epsilon^2 integral_boundary H_E phi^2+O(epsilon^3), canceling both the linear term and the phi_0 phi_N terms. These are exactly the source's compact-variation operations, applied here without assuming minimality. Hence

J(U_epsilon;B)-J(U;B)=-q epsilon^2+R(epsilon),
|R(epsilon)|<=K |epsilon|^3 for |epsilon|<=epsilon_0,

for finite K and positive epsilon_0 depending on the fixed collar and finite smooth norms of U and phi. If K=0, any nonzero |epsilon|<=epsilon_0 works. Otherwise choose

0<|epsilon|<=min(epsilon_0,q/(2K)),

which gives J(U_epsilon;B)-J(U;B)<=-q epsilon^2/2<0. This is a genuine Sobolev competitor, not a stationary gluing. To keep a smooth vector-field deformation interpretation, the classical Robin criterion supplies it; for the displayed energy comparison only the admissible Sobolev path is needed.

The form estimate supplies q relative to a quadratic norm of phi. It does not supply a uniform epsilon_0 or K: those involve collar reach, higher derivatives, and positivity away from the side boundary. Nor is a sequence witnessing the failure of such uniform bounds constructed here. Thus the missing quantitative nonlinear step is precisely identified without claiming that it is impossible.
