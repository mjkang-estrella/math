# I277 independent reconstruction: logarithmic ball–slab contact

2026-10-12. **Verdict: PASS for the complete exact claim.** This is the first independent proof gate of the authenticated I275 proposal, not a contribution decision or an acceptance/count change. There is no inferred earlier gate. I274 identifies the original unpaid steps; I275 proposes to close them. I269's checked predecessor supplies a comparison mechanism, not this new theorem.

## 1. Claim, authentication, and exact dependency boundary

Let T=R^3/Z^3 carry the unit cubic flat metric, and let P be De Giorgi perimeter. Fix a single R in (1/(2pi),1/3). For sufficiently small epsilon>0 set

    A=4pi R^3/3, r=R-epsilon, B_epsilon=2r,
    L_R(epsilon)=inf{P(E)+P(F)-4pi R^2-2:
                     E subset F a.e., |E|=A, |F|=B_epsilon}.

The class is ALL finite-perimeter pairs. The conclusion checked here is

    lim_(epsilon down to 0) |log epsilon| L_R(epsilon)/epsilon^2=2pi.

All constants may depend on fixed R. No endpoint-uniform conclusion is made. There is one prospective finding, not separate findings for capacity, the upper construction, or regularity. The project target of twenty substantial findings and every count remain unchanged.

I275 has 141 lines and SHA256 ab1a54ce81fc0047d05edc343ab6c65ac00e2a62fcc4515725df748c7aaf693f. This matches both the detached assignment and I275's manifest. That manifest is itself fully read and separately hashed. All new deductions below are independently checked. No title, parent status, or predecessor PASS substitutes for a deduction.

The stipulated OpenAI dependency is the actual family-354 Theorem intro:main at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. The complete retained entry TeX and bibliography were read. The only advanced external regularity input is AFM Definition 2.5/Theorem 4.2, read from their complete retained page excerpts. Ordinary BV compactness, submodularity, change of variables, finite-dimensional inverse/implicit functions, Poincare inequalities, and sphere spectral calculus are used in their standard forms and specialized explicitly below. No cluster theorem, CMC assertion at contact, or graph regularity of arbitrary near-minimizers is assumed.

## 2. Strict scalar branches, including complements

The actual profile is I(V)=min{(36pi)^(1/3) v^(2/3),2sqrt(pi v),2}, where v=min(V,1-V), with every finite-perimeter equality case classified.

The inner volume A is below 4pi/81 because R<1/3, and below 1/2. Its profile is 4pi R^2 and only balls of radius R minimize. For the outer volume, the limiting 2R satisfies

    1/pi < 2R < 2/3 < 1-1/pi.

For all sufficiently small epsilon, B_epsilon stays in (1/pi,1-1/pi), so its profile is exactly 2. If B_epsilon<=1/2, its minimizers are coordinate slabs of width B_epsilon. If B_epsilon>1/2, the theorem gives complements of coordinate slabs of width 1-B_epsilon. On the normal coordinate circle, that complement is an occupied interval of length B_epsilon, hence again a coordinate slab with two faces. It is not a different high-volume tube or ball branch. At R=1/4 the limiting half-volume slab is handled by the same classification and occupied-side selection.

Thus the separate deficits P(E)-4pi R^2 and P(F)-2 are nonnegative for every admissible pair. The fixed lower endpoint R>1/(2pi) is needed for the strict outer slab branch, not for a missing spherical gap.

## 3. Logarithmic cutoffs and their corners

Write ell=|log epsilon|, fix small delta>0, and set a=sqrt(epsilon) ell. Eventually a<<delta. In an embedded planar polar chart use a cutoff equal to one on rho<=a, zero on rho>=delta, and log(delta/rho)/log(delta/a) on the intermediate annulus before smoothing. Put H=log(delta/a)=ell/2-log ell+log delta.

Direct integration with area element 2pi rho d rho gives

    integral |D chi|^2=2pi/H,
    integral chi^2=O_delta(H^-2)+O(a^2),
    integral chi=O_delta(H^-1)+O(a^2),
    ||D chi||infinity=O(1/(a H)).

For example, the substitution s=log(delta/rho) makes the annular Lp integral a constant times delta^2 H^-p integral_0^H s^p exp(-2s) ds. The core has area O(a^2). These statements remain true with nonnegative smooth corner roundings supported on [a,2a] and [delta/2,delta], maintaining the stated constant core and compact support. The derivative in each rounding interval is O(1/(aH)) or O(1/(delta H)) respectively, and its squared-gradient integral is O(H^-2). Removing the original contributions on those intervals also changes energy by only O(H^-2). Smooth flat-ended interpolations can match the logarithmic profile and preserve bounded amplitude. No singular rim perimeter is left uncounted.

Use two spherical polar charts with horizontal reference coordinate y. Their reference metric is I+yy^T/(R^2-|y|^2), so the area and Dirichlet distortions on a fixed small chart are 1+O_R(delta^2). The top and bottom spherical supports are disjoint. The two flat faces are separate copies of the unit transverse torus. Consequently each of the four cutoffs has leading energy (2pi/H)(1+O_R(delta^2)+o_epsilon(1)); on the faces there is no curved metric factor.

## 4. Exact upper volumes and full containment

Fix eta>0 and t=(1+eta)epsilon/2. Relative to B_R(0) and the slab -r<z<r, put sphere normal height -t chi on both polar caps and outward face height +t chi on each corresponding flat patch.

The resulting sphere loses volume O_delta(epsilon/ell), and the slab gains that order of volume. Choose a smooth sphere bump on a fixed equatorial free patch, and a smooth face bump on a fixed transverse patch outside the ball projection. Their supports are disjoint from the cutoff supports. The derivatives of their respective volume maps at zero are nonzero. The two volume equations depend on independent bump parameters; they have a diagonal invertible derivative, uniformly for small epsilon. Their second derivatives are uniformly bounded. The inverse-function argument therefore supplies exact corrections with parameters O_delta(epsilon/ell), not merely first-order cancellation. The sphere correction expands its free patch and the outer correction contracts a free face patch; both have a fixed positive gap from the other interface. Their H1 squared costs are O_delta(epsilon^2/ell^2). Disjoint supports remove cutoff/bump Dirichlet cross terms. Every unscaled graph C1 norm tends to zero: the cutoff contribution is at most O(epsilon/(a ell)) and the bump contribution is O_delta(epsilon/ell).

For actual horizontal |x|<=a/2, the radial contraction changes the reference horizontal coordinate by a factor 1+O(epsilon), so it still lies in the constant spherical core. The exact vertical contraction there is t(1+o(1)), uniformly; the face expansion is exactly t. The relative gain is (1+eta+o(1))epsilon, strictly exceeding the imposed thinning epsilon. This verifies both contacts.

Away from this core but still near a pole, original sphere–face separation grows quadratically and is at least c_R a^2. Since a^2/epsilon=ell^2 tends to infinity, it pays every O_delta(epsilon) normal displacement and the thinning. This statement may be checked on boundary directions, avoiding a spurious unbounded vertical conversion near the equator: actual and reference transverse radii differ by 1+o(1), and a boundary point with actual |x|>a/2 has reference transverse radius at least a/3. Its original vertical gap is at least c_R a^2; its actual vertical-coordinate change is bounded by its normal displacement. Outside fixed polar charts the original gap is uniformly positive. The free corrections are supported in that separated region, where their small parameters preserve the gap. Thus the whole inner boundary lies between the two actual outer faces.

For small epsilon the inner radial graph bounds a compact region in one Euclidean lift, and both outer faces delimit the occupied slab interval, of length below one. At every transverse x, a nonempty compact inner vertical slice has its minimum and maximum z on the three-dimensional boundary: an interior extremum could be moved slightly vertically within the region. All its points therefore lie between the two outer graph heights. This proves whole-region inclusion, without requiring connected inner slices or global convexity. A torus wrapping ambiguity is absent because R<1/3 and all displacements tend to zero; the complementary gap between the outer faces also remains positive.

## 5. Upper area cost and coefficient

For a radial sphere height psi on S_R, exact fixed volume gives

    integral_S_R (psi+psi^2/R+psi^3/(3R^2))=0.

Its exact area density relative to dS_R is

    (1+psi/R)^2 sqrt(1+|grad_S psi|^2/(1+psi/R)^2).

Eliminating the linear term by that exact volume identity yields

    P(E)-4pi R^2 = (1/2) Q_B(psi)+Rem_B,
    Q_B(psi)=integral_S_R (|grad psi|^2-2psi^2/R^2),
    |Rem_B|<=C_R (||psi||infinity+||grad psi||infinity^2)||psi||H1^2.

For either flat face, area is integral sqrt(1+|D V|^2), giving Dirichlet energy divided by two and an error bounded by C||D V||infinity^2 integral |D V|^2. The baseline total outer area is 2, independent of its occupied width.

The upper sphere L2 squared term is O_delta(epsilon^2/ell^2)+O(epsilon^3 ell^2), both o(epsilon^2/ell); so is the bump cost. The remainder is also o(epsilon^2/ell) by the unscaled C1 bound. Each of four patches pays (1/2)t^2(2pi/H), up to the fixed curved-metric loss. Thus

    limsup ell L_R(epsilon)/epsilon^2
        <=2pi(1+eta)^2(1+O_R(delta^2)).

Epsilon tends to zero with delta,eta fixed, then delta and eta tend to zero. This gives the rigorous limsup<=2pi and, already for any fixed choices, an O(epsilon^2/ell) bound needed below.

## 6. Exact minimizers and limiting placement

For each small epsilon the upper construction makes the admissible class nonempty. A minimizing sequence has bounded separate BV norms. Compactness yields L1 limits; the two exact volumes and a.e. inclusion persist; the perimeter sum is lower semicontinuous. Therefore an exact paired minimizer exists.

Choose a sequence realizing the lower limit of ell L_R/epsilon^2, and an L1-convergent subsequence of its exact minimizing pairs. The upper bound and separate nonnegativity imply that each perimeter tends to its own scalar minimum. Lower semicontinuity and the limiting scalar lower bounds force equality in both limits. The limit is a radius-R ball nested in an occupied coordinate slab of width 2R.

The ball's projection on the slab normal coordinate circle is an interval of length 2R. Inclusion a.e. forces that projection interval to lie in the occupied slab interval: otherwise an open positive-volume part of the ball would lie outside. Equal interval lengths force equality of the intervals, hence the ball center is the slab midpoint in the normal direction. This also handles the complement branch after selecting its occupied interval. A common translation and a signed coordinate permutation put the limit at B_R(0) inside -R<z<R. The transverse ball center is absorbed by the common translation, to which the flat limiting slab is invariant. No arbitrary torus rotation is invoked.

## 7. Common two-volume correction for measurable pairs

Fix a small ambient sphere free patch near the equator, wholly inside the limiting slab. Choose a smooth field X_1 there with positive sphere flux. Its limiting inner volume derivative is c_1>0, and its outer derivative is zero because its support lies inside the slab and the integral of a compactly supported divergence is zero. Fix a small face patch with transverse coordinate outside the limiting ball projection, choose X_2 with positive face flux, and obtain inner derivative zero and outer derivative c_2>0. Such patches exist for every fixed R<1/3. Their supports may be fixed once the limit is normalized.

Let Phi_s be the composition of the two ambient flows, and J_s its Jacobian. For ANY measurable A',B' near the limit, their volume map is

    V_A',B'(s)=(integral_A' J_s, integral_B' J_s).

It is C2 in the two parameters, with uniform derivative bounds on the unit torus. At the limiting pair, D V(0)=diag(c_1,c_2). Changing the sets changes each derivative by at most a constant times their L1 distance; changing s has a uniform Lipschitz bound. Therefore fixed set/parameter neighborhoods have a uniformly invertible derivative. A uniform inverse-function argument corrects target volume errors of summed magnitude q with |s|<=Cq, for small q.

The same diffeomorphism applied to both sets preserves inclusion. Its cofactor estimate gives

    P(Phi_s(A'))+P(Phi_s(B'))
       <=(1+C|s|)(P(A')+P(B')).

For bounded total perimeter this costs O(q). The competitor need not have a smooth or clean free patch. The patches determine the derivative at the limiting pair only; all later volume formulas are measurable-set Jacobian integrals. Nor must the correcting flow avoid the scalar comparison ball or leave the corrected pair unchanged outside that ball: the corrected pair competes in a GLOBAL paired problem. These are precisely the reusable I269 mechanisms, checked anew in the present geometry.

## 8. Scalar quasiminimality: unrestricted competitors and every ball

Take any scalar finite-perimeter H with H triangle E_n compactly contained in a comparison ball. If P(H)>=P(E_n), the desired scalar inequality is automatic. Otherwise P(H)+P(F_n) is bounded by a fixed M. Form

    A'=H intersection F_n, B'=H union F_n.

BV submodularity bounds their summed perimeter by P(H)+P(F_n), and they are nested. The exact pointwise identity is

    |A' triangle E_n|+|B' triangle F_n|=|H triangle E_n|.

At the original nested states (E,F)=(0,0),(0,1),(1,1), flipping H from E changes respectively B' alone, A' alone, A' alone. This proves the identity without a multiplicity factor. Thus the summed target volume error is at most the scalar symmetric difference. For sufficiently small fixed comparison radius rho_0, all such A',B' remain in the uniform correction neighborhood for a tail of the sequence and have sufficiently small errors. Correct their volumes by the common flow and apply global paired minimality. Cancelling P(F_n) gives

    P(E_n)<=P(H)+Lambda |H triangle E_n|.

No restriction H subset F_n was imposed. For outer scalar H use A'=E_n intersection H, B'=E_n union H. At the same three original states, a change in H from F changes B', B', or A', respectively. The total pair change is exactly |H triangle F_n|. The identical correction argument gives the outer scalar inequality. Arbitrarily large-perimeter H were included through the automatic case, not excluded.

For rho<rho_0 the symmetric difference is bounded by the Euclidean ball volume (4pi/3)rho^3; use rho_0 below injectivity radius. For every rho>=rho_0 use the trivial bound

    P(E_n),P(F_n)<=M<=P(H)+(M/rho_0^3)rho^3.

One omega covers both scalar sets and EVERY ball, center and finite-perimeter comparison set. The omega is independent of n on the required tail. This is the exact AFM Definition 2.5 contract, including comparisons without a volume constraint. There is no ordinary equal-tension cluster identification in this argument; touching interfaces can be counted twice.

## 9. AFM contract, disconnected graphs, and occupied sides

The fully read retained AFM page 7 defines omega-minimizers by P_T(E)<=P_T(H)+omega rho^N for every ball and every finite-perimeter H with E triangle H compactly contained in that ball. The fully read retained page 22, Theorem 4.2, assumes a common omega, uniformly bounded perimeters, and L1 convergence to a C2 set in T^N. It concludes, for large n, a whole-boundary normal graph with heights tending to zero in C^{1,alpha} for alpha<1/2. The source also states eventual C^{1,1/2} regularity. It does not impose connectedness, a fixed volume, scalar minimality, or a noncontact condition.

All its hypotheses are now proved for each scalar sequence on T^3. The limits are the smooth sphere and the disjoint union of two flat tori. The theorem therefore applies separately to both interfaces. Their mutual limiting tangency is irrelevant to this scalar application. AFM presents this established classical result with attribution, without proving it on the retained page; its underlying regularity references are not freshly proved or stipulated as OpenAI truth.

Use the regular representatives. The whole-boundary graph conclusion excludes extra boundary components of the exact minimizers. The sphere graph bounds the near-ball region in an embedded lift. The two face graphs separate the normal circle into an occupied interval and its complementary interval at each transverse point. L1 convergence to the chosen limiting slab selects the occupied interval between the designated lower and upper faces. Even at limiting volume 1/2, the two sides differ on positive volume, so L1 convergence selects the side. Inclusion a.e. of regular representatives implies inner boundary containment in the closure of the outer occupied side: otherwise open inner points near an excluded boundary neighborhood would violate inclusion on positive volume. This pays the pointwise contact inequalities used later.

## 10. Reference centers and exact means

For a C1-small radial graph, its three l=1 moments depend C1 on its nearby reference center. At the zero graph their derivative is minus the Gram matrix integral_S_R omega_i omega_j=(4pi R^2/3)delta_ij. The implicit-function argument therefore chooses a nearby center with exactly zero l=1 moments. Only the reference center changes; the actual inner set is not independently moved.

Rewrite the outer face graphs over z=+r_n and z=-r_n with outward heights V_n^+,V_n^-. Their exact occupied volume is

    2r_n+integral_T2 (V_n^++V_n^-).

It follows that the sum of their means is zero exactly. Translating the reference slab center axially by q changes V^+ to V^+-q and V^- to V^-+q. Taking q equal to the upper mean makes BOTH means zero exactly. Changing reference width from R to r_n, and this reference translation, preserve C1-smallness.

A common translation then fixes the sphere reference center transversely and the slab reference center axially at zero. The remaining sphere axial reference center is h_n->0. Both actual sets undergo the same translation, and their nesting is retained. Slab functions are translated in their transverse arguments. There is no independent physical motion designed to erase h_n.

The exact sphere volume identity in Section 5 gives its constant mean b_n=O_R(||psi_n||L2^2), not b_n=0. This distinction matters for coercivity and the low-mode error. It also remains valid for a reference sphere centered at axial height h_n, because Euclidean ball volume is translation invariant in the embedded torus chart.

## 11. Coercivity and the smaller H1 scale

The centered sphere spectrum for Q_B is [l(l+1)-2]/R^2. With l=1 absent, all l>=2 modes have a uniform H1 coercivity gap. The constant contribution is negative but quadratic in b_n. Write psi=b+f with zero-mean f and no l=1 components. The exact volume identity and b->0 imply |b|<=C_R||f||L2^2 after absorbing the b^2 term. Therefore b^2=o(1)||f||H1^2. The sphere area remainder is also o(1)||psi||H1^2 by unscaled C1-smallness. These terms can be absorbed into the positive gap, so

    P(E_n)-4pi R^2 >=c_R ||psi_n||H1^2.

Each exactly mean-zero V_n^pm satisfies the period-one torus Poincare inequality. The exact flat area expansion and C1-smallness similarly give

    P(F_n)-2 >=c_R (||V_n^+||H1^2+||V_n^-||H1^2).

The upper estimate and separate nonnegativity now prove

    ||psi_n||H1+||V_n^+||H1+||V_n^-||H1
       =O_R(epsilon_n/sqrt(ell_n)),
    |b_n|=O_R(epsilon_n^2/ell_n).

Substituting this scale into the same relative error bounds proves a total area remainder o(epsilon_n^2/ell_n). No normalized C1 bound or pointwise O(epsilon_n) height bound has been derived or used. In dimension two the latter would not follow from this H1 estimate.

## 12. Exact polar vertical heights and the lower-face sign

Fix small delta and work at the same actual transverse coordinate x with |x|<2delta. Write s_0(x)=sqrt(R^2-|x|^2). The inner graph has physical top and bottom heights

    z_inner^+=h_n+s_0+W_n^+,
    z_inner^-=h_n-s_0-W_n^-.

The occupied outer interval has endpoint heights r_n+V_n^+ and -r_n-V_n^-. Actual inclusion gives EXACTLY

    V_n^+-W_n^+ >=epsilon_n+h_n-[R-s_0(x)],
    V_n^--W_n^- >=epsilon_n-h_n-[R-s_0(x)].

In particular the lower inequality has -h_n: starting with h_n-s_0-W^- >=-r_n-V^- and rearranging gives V^--W^- >=s_0-r_n-h_n. This is the required sign, not an upper-face convention copied to the bottom.

If p_n(x)=psi_n(F_n(x)) is the radial height at the actual spherical direction corresponding to x, its vertical height relative to the sphere is sqrt((R+p_n)^2-|x|^2)-s_0. Rationalization yields

    W_n(x)=A_n(x) psi_n(F_n(x)),
    A_n(x)=(2R+p_n(x)) /
            [sqrt((R+p_n(x))^2-|x|^2)+sqrt(R^2-|x|^2)].

The identity is valid with p positive, negative, or zero, by continuous extension; its denominator stays uniformly positive in these polar charts. It applies to the bottom using downward rather than upward height, with no extra sign. The h_n translation cancels in this relation. This is an exact multiplicative identity, not a pointwise Taylor remainder asserted small relative to epsilon_n.

## 13. Actual coordinate map and derivative estimates

For explicit coordinates, parameterize the reference upper or lower sphere by

    q_pm(y)=(y, +/-sqrt(R^2-|y|^2)),
    p_ref(y)=psi_n(q_pm(y)).

Its actual horizontal projection is

    G_n(y)=(1+p_ref(y)/R)y,
    D G_n=(1+p_ref/R)I+(y/R) tensor D p_ref.

Unscaled C1-smallness implies D G_n=I+o_n(1) uniformly on a fixed polar chart. Moreover, G_n-id is uniformly small and maps a slightly enlarged chart across |x|<2delta. It is injective there for large n (its derivative differs uniformly from I by less than one), with inverse J_n. Thus F_n(x)=q_pm(J_n(x)) is the actual map into the reference sphere, not the undeformed projection. Its derivative and Jacobian are controlled, and reference spherical metric distortions are 1+O_R(delta^2)+o_n(1). Enlarging the original chart to, for example, 3delta justifies coverage of the 2delta disk; the two images remain disjoint for small fixed delta.

View A_n as the smooth function B(p_n(x),x) given above. On this fixed compact coordinate range, B(0,x)=R/s_0(x), B(p,0)=1, B=1+O_R(delta^2)+o_n(1), and its partial x derivative is O_R(delta). Its partial p derivative is bounded; D p_n=o_n(1) follows from D J_n bounds and C1-smallness. Therefore

    A_n=1+O_R(delta^2)+o_n(1),
    |D A_n|<=C_R delta+o_n(1).

Only first derivatives are needed; no unproved C2 convergence enters. Uniform suprema of p_n or D p_n are never divided by epsilon_n. These estimates are geometric smallness statements, sufficient for multiplicative energy control, not o(epsilon_n) pointwise additive expansions.

## 14. Low modes, transformed high modes, and mean cost

Fix an integer N>=2, before taking n to infinity. Decompose the centered sphere height orthogonally as

    psi_n=b_n+l_n+k_n,
    l_n=sum_(l=2,...,N) psi_n,l,
    k_n=sum_(l>N) psi_n,l.

Finite-dimensional norm equivalence and the H1 scale give

    ||l_n||C1<=C_(R,N) epsilon_n/sqrt(ell_n)=o_N(epsilon_n),
    |b_n|=O(epsilon_n^2/ell_n)=o(epsilon_n).

Define W_high^pm=A_n^pm k_n(F_n^pm), with A_n and F_n taken from the FULL ACTUAL graph. Then

    W_n^pm-W_high^pm=A_n^pm(b_n+l_n)(F_n^pm)=o_N(epsilon_n)

uniformly on the charts, since A_n is uniformly bounded. No expansion of the argument of k_n has been made. Neither high-mode sup norm nor an H1 point trace is used to bound this difference. This is exactly where fixed finite modes, rather than an n-dependent spectral split, are essential.

## 15. Local high-mode energy and the Jacobi potential

Differentiating W_high gives A D(k composed F)+k composed F D A. For fixed delta and any xi>0, Young's inequality bounds its squared norm by (1+xi)|A D(k composed F)|^2+(1+xi^-1)|k composed F D A|^2. Change variables using the ACTUAL inverse map and the reference metric. The two spherical patches are disjoint, so their integrals do not duplicate sphere energy. This proves

    sum_pm integral_(|x|<2delta) |D W_high^pm|^2
      <=(1+C_R delta^2+xi+o_n(1)) integral_S_R |grad k_n|^2
           +C_(R,delta,xi) integral_S_R k_n^2.

Constants may be increased to absorb products such as xi delta^2. For lambda_N=(N+1)(N+2), sphere spectral calculus yields

    integral k_n^2 <=(R^2/lambda_N) integral |grad k_n|^2,
    Q_B(k_n)>=(1-2/lambda_N) integral |grad k_n|^2.

This pays the multiplier derivative and the negative spherical potential with arbitrarily small RELATIVE loss. It does not claim that the entire spherical potential is itself lower order for an arbitrary minimizing sequence.

Orthogonality gives Q_B(psi_n)=Q_B(b_n)+Q_B(l_n)+Q_B(k_n). The low Q_B(l_n) is nonnegative. The constant contribution has magnitude O(b_n^2)=O(epsilon_n^4/ell_n^2)=o(epsilon_n^2/ell_n). The full area remainder has already been paid at that same scale. Consequently, given any zeta>0, choose delta sufficiently small, then xi sufficiently small, then N sufficiently large with these two fixed, to get

    L_R(epsilon_n) >=(1-zeta)/2 * sum_pm
       integral_(|x|<2delta)(|D W_high^pm|^2+|D V_n^pm|^2)
       +o(epsilon_n^2/ell_n).

For example the ratio (1-2/lambda_N)/(1+C_R delta^2+xi+C_(R,delta,xi)R^2/lambda_N+o_n(1)) can be made at least 1-zeta. The flat-face energies permit discarding energy outside the disks. This explicitly proves the claimed coefficient recovery rather than retaining a fixed coercivity loss.

## 16. Sharing energy and the outer-annulus norm

Put Z_n^pm=V_n^pm-W_high^pm. The elementary vector inequality |a|^2+|b|^2>=|a-b|^2/2 gives

    L_R(epsilon_n)>=(1-zeta)/4 * sum_pm
       integral_(|x|<2delta) |D Z_n^pm|^2
       +o(epsilon_n^2/ell_n).

The factor is 1/4, not 1/2: each original interface area expansion carried 1/2, and displacement sharing supplies another 1/2. The inverse-map and multiplier bounds, combined with the centered H1 scale, also give

    ||Z_n^pm||H1(D_2delta)=O_(R,delta,N)(epsilon_n/sqrt(ell_n)).

Each Z is C1 for fixed n because psi is C1 and only smooth finite modes were subtracted. There is no need to pass to a normalized H1 limit, which would forget the shrinking contact set.

## 17. Radial averages, outer radius, and absence of a point trace

For any such C1 Z, define m(rho)=(2pi)^-1 integral_0^(2pi) Z(rho,theta) dtheta. Jensen on each circle, discarding angular energy, then weighted Cauchy–Schwarz give for 0<a<b

    integral_(a<|x|<b)|D Z|^2
       >=2pi integral_a^b rho |m'(rho)|^2 d rho
       >=2pi [m(a)-m(b)]^2/log(b/a).

This follows directly from m(a)-m(b)=-integral_a^b m'(rho) d rho and integral_a^b d rho/rho=log(b/a). It is a circle-to-circle capacity estimate. No evaluation at rho=0 occurs, and no bounded point trace of an H1 function in dimension two is invoked. For general H1 functions one could use almost-everywhere radii, but the actual finite-n graphs already are C1.

Polar integration and Jensen give

    integral_delta^(2delta) rho |m(rho)|^2 d rho
       <=(2pi)^-1 ||Z||L2(D_2delta\D_delta)^2.

Therefore some b_n in [delta,2delta] has |m(b_n)|<=C_delta||Z||L2=o(epsilon_n). Choose this radius separately at the two poles. It may depend on n and the sign; log b_n stays bounded with delta fixed. The local norm rather than an asserted global mean of Z supplies this outer estimate. The two mean-zero face functions and the small sphere mean were already needed for the global H1 scale, not for declaring this particular local average zero.

## 18. Shrinking-circle obstacle and arbitrary axial drift

Fix c>0 small and set a_n=c sqrt(epsilon_n). Eventually a_n<delta. At every point on that circle the fixed sphere satisfies

    R-s_0(x)=c^2 epsilon_n/(2R)+O_(R,c)(epsilon_n^2).

The exact two inclusion inequalities and uniformly o_N(epsilon_n) discarded low part imply

    m_n^pm(a_n)>=[1-c^2/(2R)+o_n(1)]epsilon_n +/- h_n.

Subtract the o(epsilon_n) outer m_n^pm(b_n), decreasing the common o_n(1) if necessary to cover both signs. Since an inequality d>=d_0 only bounds d^2 below by (d_0)_+^2, retain POSITIVE PARTS. The capacity bound gives

    integral_D_2delta |D Z_n^pm|^2
      >=(4pi+o_n(1))/ell_n *
           ([1-c^2/(2R)+o_n(1)]epsilon_n +/-h_n)_+^2.

Indeed log(b_n/a_n)=ell_n/2+log(b_n/c), uniformly for b_n in the fixed outer annulus. The coefficient's relative error is uniform independently of h_n. The small additive errors are o(epsilon_n), independently of the size of h_n/epsilon_n. They are placed INSIDE the positive part rather than absorbed into a nonexistent O(epsilon_n) drift assumption.

For any a>=0 and any real h,

    (a+h)_+^2+(a-h)_+^2>=2a^2.

If |h|<=a the left side is 2a^2+2h^2; if |h|>a it is (a+|h|)^2>=4a^2. This covers unrestricted axial drift, even drift much larger than epsilon_n. One can subsequently bound h_n from the upper energy, but the proof does not need that circular route. Taking c small ensures the shared a_n coefficient in this application is positive for large n.

## 19. Limit order and unrestricted lower conclusion

Combining the last estimates gives

    liminf_n ell_n L_R(epsilon_n)/epsilon_n^2
      >=2pi(1-zeta)(1-c^2/(2R))^2.

The quantified order is: given zeta, fix small delta; then small xi; then sufficiently large FINITE N; fix c>0; finally let n tend to infinity. The constants in the discarded low-mode bound may grow with N, but N is fixed before n, so that bound is o(epsilon_n). The outer-annulus constants may grow as delta shrinks, but delta is also fixed before n. The radius a_n is eventually smaller than delta for every fixed c. After obtaining the displayed inequality, c and zeta can tend to zero. Equivalently it holds for every such fixed choice; no diagonal uniformity is required. This is compatible with the separate upper order epsilon first, then delta and eta.

The chosen sequence realized the lower limit of the exact infimum; extraction and common normalizations change neither value nor volumes. Hence the lower limit of ell L_R/epsilon^2 is at least 2pi. Section 5 proves the reverse upper limit, so the complete limit is 2pi.

Every original admissible pair has energy at least its exact paired minimum. Therefore arbitrary finite-perimeter competitors, including nonsymmetric pairs, extra components, or rough boundaries, are covered. AFM was applied only after exact minimizing replacement and proved scalar quasiminimality. The proof does not silently replace the original admissible class by a graph or smooth class, nor settle only a restricted lower bound or a limsup.

## 20. Proof disposition and literature boundary

No substantive gap or necessary repair remains in the authenticated proposed mechanism. The potentially dangerous steps are resolved by the exact actual-map multiplication, fixed low-mode removal, high-mode spectral absorption, local outer-radius selection, the correctly signed bottom constraint, and positive-part drift inequality. C1-smallness alone is used only for relative geometric/area estimates; it is never promoted to an arbitrary o(epsilon_n) additive expansion. Circle constraints at finite n replace the unavailable H1 point trace. The upper competitor has actual rounded corners, exact volumes, and whole-region nesting.

This PASS relies on the stipulated finite-perimeter profile/classification and the established external AFM improved-convergence theorem after checking its exact contract. The latter's underlying classical monographs were not read, and no full AFM proof rederivation is claimed. Retained-source provenance, read limits, and authentication boundaries are specified in the companion records.

I276 documents classical logarithmically corrected droplet compression under rigid confining planes. That precedent and the elementary halving of cost when both interfaces move do not supply this all-BV global minimum theorem. Conversely, this proof verdict establishes no worldwide novelty or substantial-contribution verdict. No count increment is authorized or made. I269 is a different circle-contact/ball–tube theorem, not evidence that the new shrinking-circle capacity argument was already validated.
