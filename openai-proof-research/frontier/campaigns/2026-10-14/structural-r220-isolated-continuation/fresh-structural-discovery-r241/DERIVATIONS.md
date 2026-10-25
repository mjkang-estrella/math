# Source366 working derivations — PREFREEZE

No proposed new theorem is frozen. These are author calculations, not independent grades.
Runtime checked live: Codex / gpt-6-astra / xhigh / ultrafast. Immutable source revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb and its operative upstream proofs are assumed true.

## Exact variational interface

Omega is a bounded Lipschitz open subset of R^2, g is real and essentially bounded. K is relatively closed in Omega, H^1(K)<infinity; u belongs to L^2(Omega) and W^{1,2}(Omega minus K). All three coefficients are one:

F_g(u,K;V)=integral_(V minus K) |grad u|^2 + H^1(K intersect V) + integral_V |u-g|^2.

Absolute minimality here means every admissible (w,L) whose set symmetric difference and essential support of w-u are compactly contained in V, for every open V compactly contained in Omega. No boundary trace is prescribed in the source; arbitrary changes at the outer boundary are not compared. This is not stationarity, a quasi-minimizer class, or a stronger all-boundary global minimization assumption. Reduced means K=support_Omega(H^1 restricted to K).

The source proves local boundedness of this very u, its SBV extension, H^1(K minus J_u)=0 and K=relative closure J_u=support of its jump length. Delta u=u-g off K; no derivative of g is licensed. On a smaller smooth interior domain the pair remains an absolute minimizer.

The C^{1,alpha} full charts, finite number of global components meeting a compact region, locally finite tips and junctions, finite number of global edges meeting compact regions, and weak L^4/local strong L^p for p<4 are all paid. The last constant is allowed to depend on this minimizer and the interior region. The primary proof additionally gives |grad u(x)| <= C |x-p|^{-1/2} near each tip and bounded gradient away from tips, including near triple junctions. Fixed-pair chart radii are not uniform class radii.

## Operative compact-piece mechanism already paid

For a zero-fidelity whole-plane generalized limit with connected complement, the topological comparison constraint is empty, so all compact changes are available. Local length density and energy growth are dimensional; integral_B_R |grad v|^2 <= 2 pi R. Componentwise relative additive constants are retained until connectedness removes their ambiguity.

A bounded component can be enlarged using clopen neighborhoods in a compact truncation to a positive-length compact piece A separated from B=H minus A. Choose chi=1 near A with support disjoint from B. Project e=grad(chi v) in L^2 onto closures of whole-plane smooth gradients. Write p=e-grad phi, F=chi v-phi, f=v-F, G=grad f. The normalization at infinity gives F=O(R^{-1}), p=O(R^{-2}); div p=0 and curl p is supported on A. Whole-plane outer variations imply div G=0, and f is harmonic across A.

For any independent compact jump test h', with projected field q and potential P, translating A,F,P by t and cutting off at radius R yields, after R tends to infinity,

0 <= 2(I_p(t)-I_p(0)) + 2 sigma (I_q(t)+<p,q>) + sigma^2 ||q||_2^2,
I_q(t)=integral G(x).q(x-t) dx.

The cutoff error is O((1+|sigma|)R^{-1/2})+O((1+|sigma|)^2 R^{-2}), and dyadic interaction tails sum. Curl-support separation makes I_p harmonic in t. Its minimum at zero makes it constant; the arbitrary real sigma then kills every linear coefficient. Removal of projected gradient terms is legitimate by div G=0 and the same cutoff decay, not because G is globally L^2. Arbitrary jumps on a regular subarc give a constant normal derivative of f on every nearby translated arc. A fixed normal is therefore constant on an open disk. In dimension two, harmonicity forces f affine. Connected continuation and subquadratic growth force G=0; testing h'=h gives p=0. Removing A now lowers length. This whole rigidity mechanism is paid.

The original Deangelis v1 proof uses optimized second variations, two perpendicular translations, saturation of the full-plane Hodge projection identity, independent one-sided trace tests, and holomorphic separation. It is also paid. Its source-cited v1 mathematical text and full operative proof have been read, including recovery of the truncated first display. A v2 was identified and is being read separately before any extended claim.

## Strongest endpoint construction under examination

For one fixed interior tip p, rotate its tangent ray to the positive real axis. Write the crack as z=t+i f(t), t>=0, with f(0)=f'(0)=0 and f in C^{1,alpha}. Passing through the square-root branch maps the slit neighborhood to a domain with a C^{1,beta} boundary through zero (beta>0). The two banks are parts of the same boundary; they must not be treated as independent Dirichlet traces. If U(w)=u(w^2), conformal energy invariance gives finite H^1 energy, and the weak equation becomes

Delta U(w)=4|w|^2 [U(w)-g(w^2)], with homogeneous Neumann condition on that boundary.

Source local boundedness makes the right-hand side bounded, with an additional |w|^2 factor. A boundary C^{1,beta} estimate would give U(w)=a_0+a_1 Re w+O(|w|^{1+beta'}) and, crucially, grad U=a_1 e_1+O(|w|^{beta'}), not just a value expansion. The square-map derivative then gives

|grad u(z)|=|a_1|/(2 sqrt(|z|)) + O(|z|^{(beta'-1)/2}).

Source blow-up classification fixes |a_1|=sqrt(2/pi). A freely chosen stress coefficient is incompatible with absolute minimality. With c=1/sqrt(2 pi), delta=beta'/2>0, the resulting radial sandwich would read

|grad u|=c r^{-1/2}(1+O(r^delta)).

It predicts per-tip tail coefficient pi*c^4=1/(4*pi), spatial fourth-energy logarithmic coefficient 2*pi*c^4=1/(2*pi), and gradient-truncation logarithmic coefficient 4*pi*c^4=1/pi. These three different normalizations must not be conflated.

The immediate tasks are to justify the boundary estimate with both banks and bounded measurable forcing, control the tail remainder, compare with the full primary analysis, and decide whether anything beyond routine source plus elliptic consequences remains. No sharp-tail result or new contribution is yet claimed.


## A. Independent boundary calculation for the gradient remainder

This calculation uses the source's full C^{1,alpha} crack chart and canonical blow-up classification. It does not infer gradient convergence by differentiating a value asymptotic. Throughout, constants may depend on the fixed pair, its chosen tip chart, and a smaller compact neighborhood. It is a classical elliptic consequence, not a substantial-result nomination.

Put p=0 and rotate the outward tangent ray to R_+. After reducing the chart, the entire crack is gamma(t)=t+i b(t), 0<=t<rho, with b(0)=b'(0)=0 and b in C^{1,alpha}. It is a radial graph as well, since its radial derivative is positive near zero. The slit neighborhood is simply connected. Choose the analytic square root w of z there with argument in an interval of length pi; its two boundary banks join at w=0. The square-root image near zero lies on one side of a single boundary curve.

Here is a direct check of its boundary regularity. With q(t)=b(t)/t for t>0, q(0)=0, one has

q(t)=integral_0^1 b'(vt) dv,
|q(t)-q(s)| <= [b']_alpha |t-s|^alpha/(1+alpha).

The signed parametrization of the joined boundary is

w(s)=s sqrt(1+i q(s^2)),  -sqrt(rho)<s<sqrt(rho),

where the square root in this formula is the branch near 1. For s!=0,

w'(s)=sqrt(1+i q(s^2)) + i[b'(s^2)-q(s^2)]/sqrt(1+i q(s^2)).

It extends continuously with w'(0)=1. Both b'(s^2) and q(s^2) are C^{0,alpha} on a bounded interval, so w' is C^{0,alpha}. Its real part is bounded below after shrinking. Thus the image boundary is y=h(x), with h in C^{1,alpha}, h(0)=h'(0)=0. This check includes the negative s bank; a separate arbitrary trace is not imposed there.

Let U(w)=u(w^2). Conformal invariance of the two-dimensional Dirichlet integral and source local boundedness give U in H^1 locally up to that boundary, including 0. For every compactly supported H^1 test psi on the closed half-neighborhood, psi(sqrt(z)) is an admissible fixed-K variation: its energy is finite by the same change of variables and its support has an unchanged outer collar. The weak equation becomes

integral grad U . grad psi + integral 4|w|^2 (U-g(w^2)) psi = 0.

Hence U solves a Poisson equation with bounded right-hand side and the homogeneous natural Neumann condition on the joined boundary. There is no point source at zero; the weak test class just used crosses that point. Bounded measurable g suffices, with no differentiation or boundary trace of g.

For clarity, the elementary boundary estimate needed here can be obtained by the following energy iteration. Flatten y=h(x). The transformed function V solves div(A grad V)=F in a half-ball, with A grad V . e_2=0 on its flat face, where

A = [[1,-h'],[-h',1+(h')^2]],  F=4|w|^2(U-g(w^2)) composed with the flattening.

The determinant of the flattening is one; A is uniformly elliptic and C^{0,alpha}; F is bounded. At a boundary basepoint choose linear coordinates preserving the half-space so that the frozen conormal direction is normal. In a half-ball B_r^+, let H solve the frozen-coefficient homogeneous equation with V's data on the curved face and zero conormal data on the flat face. Testing the equations with V-H, which has zero curved-face trace, and using Poincare yields

average_(B_r^+) |grad(V-H)|^2
 <= C [L^2 r^{2alpha} average_(B_r^+) |grad V|^2 + r^2 ||F||_infty^2],

where L=[A]_alpha. Constant-coefficient homogeneous conormal solutions are transformed to even harmonic functions. The mean-value estimate for their second derivatives gives, for 0<theta<1/4,

inf_ell average_(B_{theta r}^+) |grad H-ell|^2
 <= C theta^2 inf_ell average_(B_r^+) |grad H-ell|^2,

where ell ranges over constant vectors with the frozen conormal constraint. This follows by applying the mean-value inequality to each first derivative of the reflected harmonic function and integrating its gradient along line segments in B_{r/2}. Combining the last two estimates, with a frozen-conormal vector ell_k subtracted, gives

E_{k+1} <= C theta^2 E_k
 + C theta^{-2} L^2 r_k^{2alpha}(E_k+|ell_k|^2)
 + C theta^{-2} r_k^2 ||F||_infty^2,

and the minimizing slopes satisfy

|ell_{k+1}-ell_k|
 <= C theta^{-1} [E_k^{1/2}+L r_k^alpha |ell_k|+r_k ||F||_infty].

Here r_k=theta^k r_0 and E_k is the mean squared gradient error. For any 0<beta<alpha, first choose theta so C theta^2 <= theta^{2beta}/4, then choose r_0 so that the terms containing L r_0^alpha can be absorbed. Induction gives bounded slopes and E_k <= C r_k^{2beta}: the slope increments are summable because sum r_k^beta, sum r_k^alpha and sum r_k are finite; substituting their common bound in the first recurrence closes the induction since alpha>beta and 1>beta. All constants are multiplied by the initial mean energy and ||F||_infty, as usual. Approximation by smooth coefficients and data justifies the harmonic replacements for weak solutions, and the estimates pass to the limit by their energy bounds.

The same argument centered at every nearby boundary point, together with the interior harmonic-replacement argument in balls at distance comparable to the boundary, gives a C^{0,beta} representative of grad V on a smaller closed half-neighborhood. Equivalently, compare the limiting slopes of two overlapping boundary/interior balls at scale equal to the distance between their centers; their mean-error bounds imply a difference bounded by C times that distance^beta. Interior Lebesgue differentiation identifies the representative with the weak gradient. Undoing the C^{1,alpha} flattening gives grad U in C^{0,beta}. The weak conormal condition is pointwise there by continuity, so at 0

grad U(0)=a e_1.

Consequently, for a single real a_0,

U(w)=a_0+a Re w+O(|w|^{1+beta}),
grad U(w)=a e_1+O(|w|^beta).

On the slit domain, D(sqrt z) is a rotation times 1/(2 sqrt(|z|)). Therefore, with the continuous argument theta belonging to the chosen branch,

grad u(z) = a/(2 sqrt r) (cos(theta/2),-sin(theta/2))
              + O(r^{(beta-1)/2}).                                      (A1)

Additive constants and orientation have been exhibited. Let delta=beta/2>0. Rescale at zero by r^{-1/2}, subtract a_0, and use the value and gradient estimates just proved. The resulting blow-up has half-line crack and function a Re sqrt z. The source/primary canonical classification allows only a=+sqrt(2/pi) or a=-sqrt(2/pi), not zero and not a free amplitude. This identifies the coefficient without differentiating g in a domain variation. In particular,

|grad u(z)|=c r^{-1/2}(1+O(r^delta)),   c=(2 pi)^{-1/2}.                  (A2)

The signed orientation in (A1) is fixed for this tip; it does not alternate between subsequences. Both the existence of the coefficient and the gradient remainder precede the use of classification to identify it.

## B. Exact tail, angular information, and fourth-energy renormalization

Let T be the locally finite set of tips of this fixed pair. In a relatively compact neighborhood of any compact test support, choose disjoint tip balls B_{rho_j}(p_j) and use the source/primary bounded-gradient estimates on the rest, including neighborhoods of the triple junctions. Thus only those finitely many tip balls contribute for sufficiently large threshold t. This avoids overlap, artificial boundary singularities, and any sum over infinitely many points.

By (A2), for t large the superlevel set in the jth ball is sandwiched, up to the area-zero crack, between concentric disks of radii

r_-(t)=c^2 t^{-2}(1-C_j t^{-2delta_j}),
r_+(t)=c^2 t^{-2}(1+C_j t^{-2delta_j}).

To check the upper inclusion, r^{1/2} <= (c/t)(1+C r^delta) first bounds r by 4c^2/t^2, which can then be inserted in the error term. The lower inclusion is the same inequality with the opposite error. Shrinking the tip ball ensures its relative errors are below 1/2. Its outside annulus has bounded gradient. Hence

t^4 |{x in B_{rho_j}(p_j): |grad u(x)|>t}|
 = pi c^4 + O(t^{-2delta_j}) = 1/(4 pi)+O(t^{-2delta_j}).               (B1)

For phi in C_c^1(Omega), the difference phi(x)-phi(p_j) in these disks is O(||grad phi||_infty t^{-2}). The sandwich proves the vague convergence

t^4 1_{|grad u|>t} dx  -->  (1/(4 pi)) sum_{p in T} delta_p,           (B2)

with an error O(t^{-2delta_*}+t^{-2}) against phi for a finite local collection of charts. For continuous compactly supported phi, replace the t^{-2} error by its modulus of continuity at Ct^{-2}. The constants and positive delta_* here are local to the fixed pair. This calculation does not produce a class-uniform rate.

The same argument retains orientation. Let R_j rotate the positive x-axis to the outward crack tangent, and let s_j be the sign of a in (A1). Define the oriented semicircle

S_j={s_j R_j(cos(theta/2),-sin(theta/2)): 0<theta<2pi} subset S^1.

For continuous tests Phi(x,omega), compactly supported in x,

t^4 integral_{|grad u|>t} Phi(x,grad u/|grad u|) dx
 --> (1/(4 pi^2)) sum_j integral_{S_j} Phi(p_j,omega) dH^1(omega).     (B3)

Indeed, polar integration for the model gives (c^4/2) integral_0^{2pi} Phi(p_j,s_j R_j(cos(theta/2),-sin(theta/2))) dtheta. Changing to angle on the semicircle multiplies by two. The normalized gradient error is O(r^delta_j); the radial-shell error was already estimated in (B1). The curved crack shifts the argument interval endpoint by O(r^alpha), producing an angular error of that order, absorbed since delta_j<alpha. Bounded continuous tests follow by uniform continuity. In particular the full angular mass is pi/(4 pi^2)=1/(4 pi). This orientation information is an elementary polar consequence of (A1), not a new interaction operation.

For fourth energy, (A2) implies

||grad u|^4-c^4 |x-p_j|^{-2}| <= C |x-p_j|^{-2+delta_j},

an integrable error in two dimensions. For fixed disjoint tip balls define pointwise off the tips

h(x)=|grad u(x)|^4-c^4 sum_j 1_{B_{rho_j}(p_j)} |x-p_j|^{-2}.

Then h is locally L^1 in that neighborhood. This is a difference of densities at each non-tip point, not a subtraction of two divergent integrals. For smooth phi supported there, the finite part

lim_{epsilon downarrow 0} [integral_{dist(x,T)>epsilon} phi |grad u|^4
                         -(1/(2 pi)) log(1/epsilon) sum_j phi(p_j)] (B4)

exists. To see this, the h integral converges by dominated convergence, while for each ball the remaining term is

c^4 integral_epsilon^{rho_j} integral_0^{2pi}
 [phi(p_j+r e_theta)-phi(p_j)] dtheta dr/r
 +2pi c^4 phi(p_j) log rho_j.

The first integrand is O(||grad phi||_infty), hence integrable at zero. This defines a distribution (on C_c^1, and also on compactly supported Dini-continuous tests), not a positive finite Radon measure. Its reference-scale dependence is explicit in log rho_j; changing cutoffs changes the regular L^1 part in exactly the compensating way.

For a fixed bounded region V compactly contained in Omega with no tips on its boundary and with all boundary-near tips separated from V, let N=#(T intersect V). One can equivalently use a smooth region with boundary avoiding the finitely many local tips. Then the scalar distribution function has

m_V(t)=A t^{-4}+O(t^{-4-2delta_*}),  A=N/(4 pi).

The layer-cake identity, including the upper endpoint term, is

integral_{V intersect {|grad u|<=t}} |grad u|^4
 =4 integral_0^t s^3 m_V(s) ds -t^4 m_V(t).

Thus both

integral_V min(|grad u|,t)^4 - (N/pi) log t,

and

integral_{V intersect {|grad u|<=t}} |grad u|^4 - (N/pi) log t

have finite limits, differing by A. Spatial deletion has coefficient N/(2 pi), while threshold truncation has coefficient N/pi because r is of order t^{-2}. Strong L^4 fails near every tip, and without tips the fixed-pair local gradient is bounded. These conclusions are stronger descriptions of the source endpoint, but follow through the classical boundary estimate above.

An important set-boundary limitation: (B2) does not assert convergence on every relatively compact open set. A punctured disk B_r(p) minus {p} has no tip in the open set but the same tail area as B_r(p); the atom lies on its boundary. More complicated open boundaries can produce oscillating angular fractions. The vague formulation or a tip-free boundary hypothesis is necessary.

## C. Compatible exact examples and parameter checks

The empty-crack example u=g=a_0 constant has zero energy on every comparison region and is an absolute minimizer. For a nonempty tip example take the canonical global zero-fidelity cracktip (u_*,K_*) whose minimality is the classical Bonnet-David result recorded in the source and DLF Section 1.4. Restrict it to a bounded disk and set g=u_* there. It is bounded and belongs to the source's admissible class. For every compact comparison,

F_g(w,L)-F_g(u_*,K_*)
 =[E_0(w,L)-E_0(u_*,K_*)]+integral |w-u_*|^2 >=0.

This proves its exact compatibility with the coefficient-one fidelity functional. The cracktip's original global minimality is used as a paid input; no independent reading of the entire Bonnet-David monograph is claimed. Signs, translations, rotations and a common additive constant give further compatible examples with the correspondingly changed g. In these examples (B1) is exact once the superlevel disk is inside the domain; (B4) has exactly the displayed logarithmic coefficient. The amplitude cannot be altered independently: an arbitrary multiple of sqrt(r) cos(theta/2) would generally destroy the zero-fidelity minimality and is excluded by the canonical blow-up classification.

The geometry changes under a common spatial rescaling x=L y and amplitude sqrt(L): the Dirichlet-plus-length energy rescales by L, but the fidelity coefficient in the y-functional becomes L^2 and the datum becomes L^{-1/2}g(L y). This is not a family of coefficient-one examples with a fixed datum bound unless those changes are accounted for. No spurious free small-scale parameter is used here.


## D. Executing the finite-scale compact-translation reduction

The endpoint calculations above do not by themselves supply a substantial new operation. The remaining exploratory direction is an effective finite-scale exclusion of a compact cluster, which would control regularity radii and hence constants in the endpoint formulas. The following reduction records the actual errors, rather than treating qualitative blow-up compactness as a quantitative theorem.

### D1. A robust form of the source's scalar argument

Consider the source's projected fields p,q and interaction functions I_p,I_q on a translation disk B_d. Suppose the finite-scale comparison has been reduced, uniformly in q, to

0 <= 2[I_p(t)-I_p(0)] + 2 sigma L_q(t)
       +sigma^2 ||q||_2^2 + epsilon[1+sigma^2 ||q||_2^2],             (D1)

for every real sigma and |t|<d, where L_q(t)=I_q(t)+<p,q>, and I_p is harmonic. This is an explicitly conditional reduction, not an assertion that the original class has a uniform epsilon satisfying it.

Setting sigma=0 gives J(t):=I_p(t)-I_p(0)+epsilon/2 >=0. It is harmonic and J(0)=epsilon/2. The Poisson kernel on disks, or its direct maximum/minimum ratio, gives J(t)<=3epsilon/2 for |t|<=d/2. Thus

-epsilon/2 <= I_p(t)-I_p(0) <= epsilon.

The quadratic in sigma in (D1) is nonnegative for every sigma; its discriminant is nonpositive. Therefore

|L_q(t)|^2 <= (1+epsilon)||q||_2^2 [2(I_p(t)-I_p(0))+epsilon]
             <= 3epsilon(1+epsilon)||q||_2^2.                       (D2)

For epsilon<=1 this yields |I_q(t)-I_q(0)| <= 2 sqrt(6epsilon)||q||_2. When epsilon=0 it recovers the exact source conclusion. No regularity or geometry of the crack has yet been extracted from (D2); that is a separate step. The Poisson-kernel ratio follows by representing a positive harmonic function on a larger concentric circle and then letting that circle tend to radius d.

### D2. An actual finite-disk comparison with bounded forcing

Work in rescaled coordinates at a physical scale r, on a disk B_{4R} within the rescaled domain. Put

v(y)=r^{-1/2}u(x_0+r y),  g_r(y)=r^{-1/2}g(x_0+r y).

The scaled functional is E_0(v,H)+r^2 integral |v-g_r|^2. If |u|<=M and |g|<=G on the original region, fixed-set outer variations give, distributionally across H,

div m=e_r,  m=grad v,  e_r=r^2(v-g_r),  ||e_r||_infty<=r^{3/2}(M+G). (D3)

Suppose provisionally there is a compact piece A inside a fixed inner disk, separated from B=H minus A. Choose chi=1 near A supported away from B inside that disk. Extend h=chi v by zero and use the exact whole-plane projection from the source to obtain F,p. This does not assume that the finite-domain minimizer is a global minimizer. In B_{4R} minus B, f=v-F extends across A, with G_0=grad f=m-p and div G_0=e_r. Its curl vanishes there. Choose an outer cutoff eta_R, equal to one on B_R and zero outside B_{2R}. For a compact jump test h' and its projected P,q, set

D_{t,sigma}=F_t-F+sigma P_t,
V_R=v+eta_R D_{t,sigma},   J=B union (A+t).

In the inner disk this is f+F_t+sigma P_t. For translations smaller than the fixed separation, it is Sobolev off J, and its length change is exactly zero. Its outer collar is unchanged, so it is a genuine compact comparison. Choose R large enough to contain the supports of h,h' and their translations.

Define finite interactions using the compact field

I_q^R(t)=integral eta_R G_0 . q_t.

These interactions are harmonic in t even though div G_0 is not zero. Indeed, the identity Delta q=grad-perp curl q localizes the translation Laplacian to A+t; on a neighborhood of all such translates, eta_R G_0=grad f has zero curl. The resulting distributional translation Laplacian is zero. The L^2 translation pairing is continuous, so the interaction equals its smooth harmonic representative. This observation uses curl, whereas removing the projected potential later uses divergence; those two roles must not be conflated.

The source's exterior projection estimates give, for fixed h,h', a fixed translation disk, and R sufficiently large,

||grad(eta_R D)||_(L^2(annulus))
 <= C(h,h',d)(1+|sigma|)R^{-1},

and the omitted quadratic tails are at most C(h,h',d)(1+sigma^2)R^{-2}. Expanding the energy inside B_R and comparing its cross terms with I_q^R adds an annular error of the same order as the cutoff cross term. Thus the Dirichlet part yields the source quadratic inequality up to absolute error

C(h,h',d)(1+sigma^2)[R^{-1} E_R^{1/2}+R^{-2}],                    (D4)

where E_R=integral_(B_{2R}) |grad v|^2 plus a fixed quantity depending on p. This follows directly from Cauchy-Schwarz, with no subtraction of infinite energies. No uniformity in h' or in the geometry is asserted in the constant.

The fidelity difference is exactly

r^2 integral [2(v-g_r)eta_R D + eta_R^2 D^2].                       (D5)

Because F_t-F=O(|y|^{-2}) and P_t=O(|y|^{-1}) outside a fixed disk, their norms satisfy

||D||_(L^1(B_{2R})) <= C(h,h',d)[1+log R+|sigma|R],
||D||_(L^2(B_{2R}))^2 <= C(h,h',d)(1+sigma^2)(1+log R).

In the fixed inner disk, these estimates use local L^2 integrability; in the exterior they are the elementary polar integrals of the displayed decay rates. Substitution in (D5) gives the absolute bound

C(h,h',d)(1+sigma^2)
 [r^{3/2}(M+G)(1+R)+r^2(1+log R)].                                (D6)

Here R>=2 absorbs log R in the first term. No derivative of g has appeared. The source energy comparison gives E_R <= C R + C r G^2 R^2 plus the fixed p term. Thus the R^{-1}E_R^{1/2} in (D4) is bounded by

C R^{-1/2}+C sqrt(r)G+C(p)R^{-1}.

For a fixed physical outer ball, R is proportional to 1/r. Formally, if all the constants attached to h,h',d were uniformly controlled, (D4)-(D6) would be O(sqrt(r))(1+sigma^2), with smaller r^2 log(1/r) terms. This is an actual error calculation for each fixed construction. It is not a class-uniform estimate: h=chi v, the cutoff separation, the size of the chosen regular arc, and the relation between h' and q can degenerate with the sequence being blown up. The passage from (D4)-(D6) to the uniform normalization required in (D1) remains unproved.

### D3. The divergence defect in the jump-flux step

The exact finite-interaction counterpart of removing the projected potential is

I_q^R(t)=integral eta_R G_0 . (grad h')_t
          +integral [eta_R e_r+grad eta_R . G_0] phi'_t,             (D7)

where q=grad h'-grad phi'. Integration by parts proves the sign and both terms in the second integral. It is not legitimate to discard them by invoking the homogeneous source identity.

For fixed h', the forcing part is bounded by C(h')r^{3/2}(M+G)(1+R), since phi'=O(1/|y|). The outer-boundary part is bounded by C(h')R^{-1}E_R^{1/2}, since phi' has bounded L^2 norm on an annulus of comparable radii. For a one-sided strip test h'_beta with trace jump beta, supported in the inner region, integration by parts gives

integral G_0 . (grad h'_beta)_t
 = plus-or-minus integral beta(s) partial_n f(gamma(s)+t)|gamma'(s)| ds
   -integral e_r (h'_beta)_t.                                      (D8)

Thus even a successful (D2) yields an approximate weak flux condition with the additional explicit terms (D7)-(D8), not exact constancy of a normal derivative.

On a fixed small disk away from B one can solve Delta a=e_r with zero boundary values. The Green kernel bounds give ||grad a||_infty<=C d ||e_r||_infty on a smaller concentric disk. Hence f-a is harmonic there, and (D8) can be converted to an approximate harmonic flux condition locally. This removes bounded forcing on that fixed disk, but still does not propagate quantitative affinity throughout the possibly badly connected domain R^2 minus B.

### D4. What remains unproved, and why the obvious shortcuts fail

There are two separate missing uniform steps.

1. Uniform normalization of the compact projection and trace tests. The errors must be controlled by epsilon(1+sigma^2||q||_2^2), not by an uncontrolled C(h,h',d)(1+sigma^2). A vanishing separation or regular-arc radius can make these constants diverge. Even controlling a potential by its gradient requires care: for a closed-loop crack a piecewise constant interior test has q=0 but a nonzero potential. Connected complement removes that exact kernel, but does not by itself supply a quantitative Poincare constant for an arbitrary thin-neck geometry. The loop observation is an auxiliary functional counterexample, not an example in the connected-complement minimizer class.

2. Uniform propagation from a local approximate flux condition to a global quantitative energy saving. Exact harmonic unique continuation in the source is qualitative. Its use on a connected domain supplies no bound for propagation through unspecified narrow passages. One would need a proved quantitative geometric chain or an alternative variational argument with controlled constants. No such estimate has been established here from only the source's admissible data.

The fidelity cannot simply be differentiated twice to bypass these issues. On a fixed rectangle, translating the step F(x)=sign(x_1) against the bounded datum g(x)=sign(x_1) changes its fidelity energy by 4|t| times the transverse length, for small horizontal translations, with the vertical sides kept outside the comparison region. This elementary auxiliary example shows the generic absolute-value kink; it is not claimed to be an absolute Mumford-Shah minimizer or a counterexample to a quantitative theorem. For the actual minimizer class, (D5) is the justified expression, and its finite-difference estimate is what is available without extra regularity of g.

Standard compactness and epsilon regularity may produce non-effective uniform conclusions on carefully normalized compact classes. That whole operation must be paid before asserting a new result. It does not replace the two explicit estimates above, and no uniform separation, uniform count, topology-preserving approximation rate, or stability of a chosen minimizer is claimed here.

## E. Comparison and stopping scope

The strongest integrated work completed in this round is (A1)-(A2) plus (B1)-(B4), and the finite-scale reduction (D3)-(D8). The endpoint calculation includes both crack banks, bounded forcing, normalization of the stress coefficient, the whole local gradient remainder, finite overlaps, triple-junction exclusion from the tail, angular information, and both logarithmic cutoffs. It is a consequence of source geometry and standard boundary elliptic analysis. It is not offered as a distinct substantial finding merely because the distributional formulation is more explicit than the source headline.

The finite-scale comparison executes the source construction with its actual fidelity and outer-cutoff errors. Its remaining uniform normalization and propagation steps are not proved. No precise viable substantial full-scope theorem has emerged, so no theorem/proof scope is frozen, renamed, narrowed or sent for a different grade. The disposition is PREFREEZE/no nominee. This document assigns no correctness, contribution, acceptance, or campaign count. No exhaustion or worldwide-priority claim is made.
