# I346 — Moving-radius unrestricted ball/cylinder–slab crossover

Research completed 2026-10-13. **Complete research proof under the stated dependencies; TECHNICAL extension, not a substantial-finding nomination.** No independent proof/contribution gate is claimed. No shared record or accepted count is changed; no git operation or publication is performed.

## 1. Claim and exact scope

Put T=R^3/Z^3 with its unit cubic flat metric, R_*=1/3, rho_*=2/9, a_*=4pi/81, and let P be De Giorgi perimeter. For 0<epsilon<1 and R<R_* sufficiently close to R_*, define

    D_R(E,F)=P(E)+P(F)-4pi R^2-2,
    L_R(epsilon)=inf D_R(E,F),
    E subset F a.e., |E|=4pi R^3/3, |F|=2(R-epsilon).

The infimum is over **all finite-perimeter pairs**, with no symmetry, topology, regularity, connectedness or graph assumption. Let

    ell=|log epsilon|, S=epsilon^2/ell,
    delta=R_*-R, rho(R)=sqrt(4R^3/3),
    g(R)=2pi rho(R)-4pi R^2.

For every moving family R_epsilon<R_* tending to R_* with delta/S tending to lambda in [0,infinity],

    L_(R_epsilon)(epsilon)/S -> min{2pi,(2pi/3)lambda},       (1)

where the right side is 2pi when lambda=infinity. No rate, monotonicity, continuity or measurability of the moving family is required. The argument is sequential and covers every epsilon sequence tending to zero.

More precisely, there is a fixed L1 neighborhood of the endpoint ball orbit and its unrestricted localized minimum M_B(R,epsilon), defined in Section 4, such that, jointly as (R,epsilon)->(R_*,0), R<R_*,

    M_B(R,epsilon)/S -> 2pi,
    L_R(epsilon)=min{M_B(R,epsilon),g(R)}                    (2)

for all sufficiently close parameters. The cylinder localized minimum is **exactly** g(R), not merely g(R)+o(S).

Here and below an arbitrary near-minimizer means an admissible family with

    D_R(E_epsilon,F_epsilon)-L_R(epsilon)=o(S).              (3)

This explicitly fixes the error scale, including when lambda=0. Its morphology conclusion is in the paired L1 metric d((E,F),(A,B))=|E triangle A|+|F triangle B|:

* If 0<=lambda<3, its distance to K_C tends to zero. K_C consists of a radius-2/9 coordinate tube inside an occupied coordinate slab of width 2/3, with tube axis parallel to the faces. In a common normalization F={|z|<1/3}, the axis is parallel to x or y, and its normal center offset h satisfies |h|<=1/9. Arbitrary transverse translations and signed coordinate permutations are included. Every exact minimizer, for sufficiently small epsilon along this family, is an **exact** radius-rho(R) coordinate tube nested in an exact width-2(R-epsilon) coordinate slab; its offset satisfies |h|<=R-epsilon-rho(R). The minimum equals g(R).
* If 3<lambda<=infinity, the distance to K_B tends to zero. K_B consists of a radius-1/3 ball nested in a width-2/3 coordinate slab, with the ball normally centered between the two faces. Every exact minimizer is eventually a C1-small sphere graph and two C1-small slab-face graphs. Centering the reference sphere at radius R and the reference slab at width 2(R-epsilon), as in Section 7, gives H1 graph norms O(sqrt(S)) and relative normal center drift h=o(epsilon).
* If lambda=3, the distance to K_B union K_C tends to zero. Each class has an admissible family satisfying (3); alternating these families is allowed. Neither uniqueness nor exact coexistence of global minimizers for each parameter is asserted. Higher order terms can decide the exact minimizing class.

These L1 statements do not impose topology or smoothness on arbitrary near-minimizers. The stronger graph conclusions concern exact minimizing replacements only.

## 2. Dependencies and attribution

The stipulated scalar input is actual family354 Theorem `intro:main`, including its complement rule and exhaustive endpoint equality classification, at OpenAI revision `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. The actual entry theorem was read, not inferred from the catalogue. Its [pinned entry](https://raw.githubusercontent.com/openai/math/fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb/preprints/The-Isoperimetric-Conjecture-for-the-Cubic-Flat-Three-Torus-September-24-2026/build/paper.tex) has SHA256 `ab75095f542adf4073a41a26a3c3ae97be7b55fa19674ec4fb4c288f7145a813`. The complete retained entry, pinned README, preliminaries and references were read. The complete preprint path listing and family354 catalogue entry identify one manuscript package, with no listed family354 companion. No upstream proof audit is performed.

[R018](../findings/R018-ball-slab-logarithmic-contact.md), the complete [I275 proof](i275-logarithmic-contact-full-proof.md), the complete [I277 reconstruction](../experiments/i277_logarithmic_contact_proof/analysis.md), and [I283](i283-ball-slab-endpoint-obstruction.md) were read. I275's authenticated SHA256 is `ab1a54ce81fc0047d05edc343ab6c65ac00e2a62fcc4515725df748c7aaf693f`. The fixed-R theorem is not substituted with a varying R: Sections 4–7 below establish the new sequential hypotheses before carrying out its contact estimates.

The external regularity dependency is Acerbi–Fusco–Morini (AFM), Definition 2.5 and Theorem 4.2, read in the existing page-7/page-22 excerpts and checked against the [primary paper](https://cvgmt.sns.it/media/doc/paper/540/Acerbi-Fusco-Morini.FINAL.pdf). The only contract used is improved whole-boundary graph convergence for uniformly scalar quasiminimizing sets approaching a smooth limit. Their Theorem 1.1 and its gamma=0 discussion were also consulted as established local-stability precedent; the proof here derives the necessary cylinder graph inequality directly and does not assume parameter-uniform constants from that theorem.

BV compactness, perimeter submodularity, finite-dimensional inverse functions and elementary spectral/capacity calculations have their standard meanings. Full source/read boundaries and the current primary-literature comparison are in the three companion records.

## 3. Upper bounds, uniformly near the endpoint

The outer volumes eventually lie strictly in (1/pi,1-1/pi). The scalar profile therefore gives P(F)>=2, even though |F|>1/2, since the complement of a coordinate slab is another occupied coordinate slab. For R<=R_*, the inner scalar bound is P(E)>=4pi R^2. Thus D_R>=0 for every admissible pair.

Take F={|z|<R-epsilon} and E={y^2+z^2<rho(R)^2}, independent of the coordinate x. Its volume is pi rho(R)^2=4pi R^3/3 and its perimeter is 2pi rho(R). Since R_*-rho_*=1/9, rho(R)<R-epsilon with a fixed positive margin for all sufficiently close parameters. Both sets are embedded in the required transverse charts. Hence

    L_R(epsilon)<=g(R),
    g(R)/delta=4pi R^(3/2)/(1/sqrt(3)+sqrt(R))->2pi/3.        (4)

The I275 four-patch ball recovery is also uniform here. To check this independently, restrict R to a sufficiently small closed interval [R_*-kappa,R_*]. The polar metric and its derivatives, the sphere Jacobi coefficients and all reference chart radii are uniformly controlled on it. An equatorial sphere patch lies a fixed positive distance inside the slab, and an outer-face patch outside the ball projection stays a fixed positive distance from the ball. The volume derivatives on these two free patches stay nonzero. None of these statements relies on global uniqueness of the scalar ball minimizer.

For fixed small d>0 and eta>0 take a=sqrt(epsilon)ell and a smoothed radial logarithmic cutoff chi supported in |x|<d, equal to one in |x|<=a. Writing H=log(d/a)=ell/2-log ell+log d, planar integration gives

    integral |grad chi|^2=2pi/H+O(H^-2),
    integral chi^2=O_d(ell^-2)+O(a^2),
    integral chi=O_d(ell^-1)+O(a^2).

The corner smoothing has energy O(H^-2) and preserves a constant core. On the two sphere caps move inward normally by t chi, and on each slab face move outward by t chi, where t=(1+eta)epsilon/2. Independent bumps on the fixed free patches restore both exact volumes with parameters O_d(epsilon/ell). Their area costs after enforcing volume are O_d(epsilon^2/ell^2). All unscaled C1 norms tend to zero uniformly in R.

For actual |x|<=a/2, normal-to-vertical conversion gives inward displacement t(1+o(1)); together with the outer t displacement this exceeds epsilon. Outside that core the reference gap is at least c a^2, uniformly in R, until the fixed chart ends; a^2/epsilon=ell^2 tends to infinity. It pays every O_d(epsilon) displacement. Outside the polar charts all free-patch gaps remain positive. Thus the entire inner boundary lies between the two actual outer faces. A compact inner vertical slice has its extrema on that boundary, so the whole inner region lies in the outer occupied interval. No assumption on connected vertical slices is used.

The exact-volume sphere area expansion and flat-face expansions show that each of four patches pays t^2 pi/H to leading order. The sphere potential, L2 terms and correcting bumps are o(S), with constants uniform in the closed radius interval. Consequently

    limsup_(R->R_*,epsilon->0) D_R(recovery)/S
       <=2pi(1+eta)^2(1+O(d^2)).

Let eta,d tend to zero after the parameter limit. This gives the ball limsup 2pi and an O(S) bound for its localized minimum.

## 4. Endpoint compactness and separated local minima

Let B_* be the compact orbit of all radius-R_* balls, and C_* the compact union of the three coordinate-axis radius-rho_* tube orbits, in L1. They are disjoint. In fact a ball projects on any coordinate axis into an interval of length 2/3. A tube has constant cross-sectional area a_* along its own coordinate axis; therefore |C\B|>=a_*/3, and equal volumes give

    |C triangle B|>=2a_*/3.

Take once and for all eta_0=a_*/10, and write d_j(E)=dist_L1(E,j_*), j=B,C. The closed constraints d_j(E)<=eta_0 are disjoint. Define M_j(R,epsilon) by the original unrestricted paired minimization with this one additional closed constraint on E. There is no restriction on F beyond the original inclusion and volume conditions. Both local classes are nonempty for nearby parameters by Section 3. BV compactness gives exact localized minimizers.

Whenever D_(R_n)(E_n,F_n)->0 for admissible pairs with R_n->R_*, epsilon_n->0, the separate nonnegative deficits tend to zero. BV compactness and the stipulated profile give, along subsequences, simultaneous scalar equality at volumes a_* and 2/3. Exhaustive equality says that E_0 is a ball or a coordinate tube, and F_0 an occupied coordinate slab. Inclusion is closed under paired L1 convergence. A tube whose axis is normal to the faces fills the entire normal coordinate circle and cannot lie in that slab. A parallel tube has offset |h|<=1/3-2/9=1/9. A ball projects into an interval of exactly the occupied slab width, so its normal center equals the slab center. The full paired limit classes are precisely K_B,K_C defined above. Mixed positive-volume scalar phases, Delaunay modes and other equality limits are excluded by the stipulated exhaustive classification, not by an assumption on the competitors.

The localized ball minima have energy O(S)->0; the localized cylinder minima have energy at most g(R)->0, even when g(R)/S tends to infinity. For either class every limit is its own equality class: the other inner orbit is farther than eta_0. It follows that localized exact minimizers satisfy d_j(E_n)->0. Their L1 constraints are eventually interior by a fixed margin.

The same compactness applied to exact global minimizers, using the ball O(S) upper bound, puts their inner sets in one of these two neighborhoods for all sufficiently close parameters. Otherwise a sequence of counterexamples would converge to one of the two orbits while remaining outside both neighborhoods. Hence

    L_R(epsilon)=min{M_B(R,epsilon),M_C(R,epsilon)}           (5)

eventually. This argument also explains why localizing does not restrict the final global theorem: the localized minima partition every possible low-energy exact global minimizing limit.

## 5. Regularity of localized replacements

Fix any sequence of exact localized minimizing pairs and a normalized endpoint limit in its class. Every such limit, including a tube tangent to one slab face, has (i) a nonempty inner-boundary patch strictly inside the slab and (ii) an outer-face patch strictly outside the inner set. For a tube the opposite side of any tangency provides (i), and a transverse point outside its strip projection provides (ii). Choose smooth ambient fields supported on these patches. At the limiting pair their two-volume Jacobian is diagonal and invertible.

For nearby measurable pairs the volume maps are integrals of the smooth flow Jacobian over each set. L1 closeness preserves uniform invertibility. A common diffeomorphism therefore corrects total volume error q with parameter O(q). For bounded perimeter its perimeter cost and total L1 displacement are O(q); the latter is the ordinary BV transport estimate obtained by smooth approximation and integrating the flow derivative. The common map preserves inclusion.

For an arbitrary scalar inner comparison H, use (H intersection F,H union F). Submodularity bounds its total perimeter by P(H)+P(F); its total paired L1 change equals |H triangle E| exactly. For an outer comparison H use (E intersection H,E union H), with change |H triangle F|. Common correction and localized minimality therefore give, for smaller-perimeter comparisons supported in any sufficiently small ball,

    P(E)<=P(H)+C|H triangle E|,
    P(F)<=P(H)+C|H triangle F|.

Here a fixed sufficiently small comparison ball, plus the O(q) correction displacement, stays inside the eta_0 constraint because the original localized minimizer has d_j(E)->0. Thus the artificial constraint is inactive for these comparisons. Larger-perimeter comparisons give the inequality automatically. For larger balls use the bounded-perimeter trivial estimate, so a single constant gives the AFM omega r^3 comparison condition for every ball and every finite-perimeter scalar comparison. Constants are uniform along the chosen sequence.

AFM now gives global C1-small normal graphs over the smooth limiting sphere or cylinder and over both disconnected flat slab faces. L1 convergence selects the correct occupied sides. Extra components of these exact replacements are excluded by the whole-boundary conclusion. References can be moved to radii R_n or rho(R_n) and width 2(R_n-epsilon_n); those geometric changes tend to zero. Arbitrary near-minimizers have not been declared quasiminimizers or graphs.

## 6. The cylinder localized minimum is exactly g(R)

Normalize a limiting tube to the x-axis. Write its centered inner graph as

    (s,(rho+u(s,theta))cos theta,(rho+u(s,theta))sin theta),
    s in R/Z, theta in R/(2pi Z), rho=rho(R_n).

Changing the two transverse reference-center coordinates by the implicit function theorem removes exactly the moments against cos theta and sin theta. The derivative at zero is their nonsingular Gram matrix. Axial translation is a symmetry with identically zero normal component and needs no removed mode. The occupied-side conclusion gives the exact volume equation

    integral (rho u+u^2/2) ds dtheta=0.                      (6)

The exact area density is

    sqrt((rho+u)^2(1+u_s^2)+u_theta^2).

Expanding it, and eliminating its linear integral with (6), gives

    P(E)-2pi rho = Q_rho(u)/2 + Rem,
    Q_rho(u)=integral [u_s^2+rho^-2(u_theta^2-u^2)] rho ds dtheta,
    |Rem|<=o(1)||u||_H1^2,                                (7)

uniformly for rho near 2/9, since the unscaled C1 graph norms tend to zero. This also follows directly by expanding sqrt(1+t) in the exact displayed density; the coefficient errors are controlled by ||u||_infinity+||Du||_infinity^2.

On Fourier modes exp(2pi i k s+i m theta), the Jacobi eigenvalues are

    4pi^2 k^2+(m^2-1)/rho^2.

The constant mode is negative but its mean b is quadratic by (6): after absorbing b^2, |b|<=C||u-b||_L2^2. The two zero modes k=0,m=+/-1 were removed by centering. Every remaining mode has a positive gap, uniformly for rho near rho_*, because

    min{4pi^2-rho_*^-2,3rho_*^-2}
       =min{4pi^2-81/4,243/4}>0.                          (8)

The first positivity follows already from pi>3. The spectral bound also controls the full H1 norm on the remaining modes. Absorbing the quadratic-mean contribution and the remainder in (7) gives

    P(E)>=2pi rho+c||u||_H1^2                              (9)

on a tail of every localized minimizing sequence, with a uniform c>0. This is a local inequality on the replacements; P(E)>=2pi rho was never inferred globally from the scalar profile below its ball/tube transition.

Since P(F)>=2, (9) gives M_C>=g(R). The explicit centered tube/slab gives M_C<=g(R). Sequential contradiction establishes M_C=g(R) for all sufficiently close parameters, without an assumption on delta/S. Equality in (9) forces u=0, and P(F)=2 forces an exact coordinate slab. Its tube axis is parallel to its faces by inclusion, with |h|<=R-epsilon-rho(R). The same argument applies to all localized exact minimizers, yielding the classification stated in Section 1.

## 7. The ball localized lower passage is uniform

Take arbitrary R_n->R_*, epsilon_n->0 and exact ball localized minimizing pairs. Sections 3–5 give energy O(S_n), a limiting normally centered ball/slab pair, and C1-small whole-boundary graphs. Normalize the slab normal to z, remove the three spherical translation moments, and translate the reference slab center so its two outward face heights V_n^+,V_n^- have zero means separately. Exact outer volume makes their means sum to zero; a reference translation changes them oppositely. Retain the relative sphere/slab axial reference displacement h_n. These are changes of representation of the same sets, not independent physical moves.

On S_(R_n), write the sphere radial height psi_n. The exact volume identity is

    integral (psi_n+psi_n^2/R_n+psi_n^3/(3R_n^2))=0.

The spherical l>=2 eigenvalues [l(l+1)-2]/R_n^2 have a uniform gap; the mean is quadratic and l=1 is absent. The face Poincare constants are fixed. The exact-volume area expansions therefore give

    ||psi_n||_H1+||V_n^+||_H1+||V_n^-||_H1=O(sqrt(S_n)),
    D_n=Q_(R_n)(psi_n)/2
           +(1/2)sum_pm integral |grad V_n^pm|^2+o(S_n),
    Q_R(psi)=integral_S_R (|grad psi|^2-2psi^2/R^2).         (10)

All remainders are relative o(1) times H1 squared, hence o(S_n). Constants are uniform near R_*. They do not involve the globally competing cylinder branch.

Here are the exact chart and localization estimates needed to transfer the R018 lower argument, rather than only its fixed-R conclusion. On horizontal disks |x|<2d at the two poles, let W_n^pm be the actual outward vertical sphere heights relative to h_n+sqrt(R_n^2-|x|^2) and the corresponding lower reference. Actual inclusion gives

    V_n^pm-W_n^pm>=epsilon_n +/-h_n
                        -[R_n-sqrt(R_n^2-|x|^2)].          (11)

If p_n(x)=psi_n(F_n(x)), with F_n the ACTUAL inverse horizontal parametrization into the reference sphere, rationalization gives exactly

    W_n=A_n psi_n composed F_n,
    A_n=(2R_n+p_n)/[sqrt((R_n+p_n)^2-|x|^2)
                                  +sqrt(R_n^2-|x|^2)].     (12)

Indeed the reference horizontal map in a polar coordinate y is (1+psi_n(y)/R_n)y. Its derivative is I+o(1); it has a controlled inverse on a slightly enlarged fixed chart. Uniformly for R_n near R_*, the metric distortion and A_n are 1+O(d^2)+o(1), and |grad A_n|<=Cd+o(1). No arbitrary C1 coordinate error is divided by epsilon_n.

For a fixed N decompose psi_n=b_n+l_n+k_n into the constant, spherical degrees 2 through N, and degrees above N. From (10), b_n=O(S_n) and ||l_n||_C1=O_N(sqrt(S_n))=o_N(epsilon_n). Keep the actual A_n,F_n in W_high^pm=A_n^pm k_n composed F_n^pm, so W_n-W_high=o_N(epsilon_n) uniformly. Young's inequality and change of variables give, for fixed d,xi>0,

    sum_pm integral_D_(2d) |grad W_high^pm|^2
       <=(1+Cd^2+xi+o(1)) integral_S_(R_n) |grad k_n|^2
                           +C_(d,xi) integral_S_(R_n) k_n^2.

The two polar patches are disjoint. The high-mode bound

    integral k_n^2<=R_n^2/[(N+1)(N+2)] integral |grad k_n|^2

absorbs both the multiplier derivative and the negative Jacobi potential. The low Jacobi energies are nonnegative and the constant cost is o(S_n). For every zeta>0 choose d small, then xi small, then N large, all fixed before n. With Z_n^pm=V_n^pm-W_high^pm this proves

    D_n>=(1-zeta)/4 sum_pm integral_D_(2d)|grad Z_n^pm|^2
                                                    +o(S_n),
    ||Z_n^pm||_H1=O_(d,N)(epsilon_n/sqrt(ell_n)).            (13)

The factor 1/4 includes the 1/2 area factor and the 1/2 energy-sharing inequality. These uniform estimates are precisely I275's local mechanism with the uniformly controlled R_n reference geometry; their proof does not use a uniform global scalar uniqueness gap.

For the circle average m(r) of Z, Jensen and weighted Cauchy–Schwarz give

    integral_(a<|x|<b)|grad Z|^2
       >=2pi[m(a)-m(b)]^2/log(b/a).                        (14)

The L2 estimate in (13) chooses b_n in [d,2d] with m(b_n)=o(epsilon_n), separately for each pole. On a_n=c sqrt(epsilon_n), (11) and the removed low modes give

    m_n^pm(a_n)>=[1-c^2/(2R_n)+o(1)]epsilon_n +/-h_n.

As log(b_n/a_n)=ell_n/2+O(1), (13)–(14) imply the lower bound using positive parts, not a point trace:

    liminf D_n/S_n>=2pi(1-zeta)(1-c^2/(2R_*))^2,

because (s+h)_+^2+(s-h)_+^2>=2s^2 for every s>=0 and every real h. Let c,zeta tend to zero after n. Together with Section 3 this proves M_B/S->2pi jointly. No relation between delta_n and S_n was needed.

For completeness this also gives the stated axial drift of ball localized exact minimizers. Keeping the positive-part sum instead of discarding drift, the O(S_n) bound first gives |h_n|=O(epsilon_n). On any subsequence h_n/epsilon_n->H, the same estimates and M_B/S_n->2pi yield

    2pi>=pi[(1+H)_+^2+(1-H)_+^2].

Letting the fixed c,zeta go to zero justifies this expression. The right side is strictly larger than 2pi unless H=0. Thus h_n=o(epsilon_n). No drift estimate is asserted for rough near-minimizers without a graph representation.

## 8. Global limit and arbitrary near-minimizers

Equations (5), (9) and Section 7 give (2). Equation (4) then gives (1), including lambda=0 and lambda=infinity. In the latter case g/S->infinity while M_B/S->2pi, so the ball localized minimum wins. This proves the unrestricted infimum; the regularity argument was only a justified replacement step.

For any family satisfying (3), D_R=O(S)->0 by the global ball upper bound. Section 4 gives dist((E,F),K_B union K_C)->0. If a subsequence approaches K_B, its inner sets eventually satisfy the ball constraint and their energy is at least M_B. If it approaches K_C, their energy is at least M_C=g(R). When lambda<3, the normalized gap between the ball cost 2pi and the achieved cost (2pi/3)lambda is strictly positive; a ball subsequence contradicts (3). When lambda>3, including infinity, the cylinder cost exceeds the achieved ball cost by a positive normalized amount; a cylinder subsequence contradicts (3). Compactness converts these exclusions into the stated full-family distances to the selected paired class. There is no graph assumption on these sequences.

At lambda=3, the centered cylinder competitor has D/S->2pi. An asymptotically optimal ball localized minimizing family also has D/S->2pi. Since L/S->2pi, both satisfy (3), and their endpoint inner orbits remain a positive L1 distance apart. Thus asymptotic uniqueness would be false. At exact finite parameters (2) decides the class but provides no second-order tie rule.

## 9. Contribution verdict and remaining limits

The moving-radius theorem is proved here under the specified scalar and AFM inputs. Its main additional work is separation of two compact equality orbits, inactive-neighborhood replacement, a strictly positive cylinder Jacobi spectrum and uniformity of the **already existing** R018 contact proof. The scalar transition is a crossing of two nondegenerate local wells: at the endpoint the sphere has l=2 gap 36 and the cylinder has gap 4pi^2-81/4>0 after translations. There is no new vanishing Jacobi mode or new singular capacity mechanism to pay for.

The sharp logarithmic lower passage remains R018's contribution. The cylinder lower passage is ordinary strict local stability; the near-minimizer selection is comparison of separated costs. The additional exact cylinder-phase classification and ball reference-drift consequence are useful precision, but neither supplies a new substantive mechanism. **Research assessment: TECHNICAL / not substantial.** This assessment does not rely on an unsuccessful exact-title search or on the project count. There is no proposed count increment or new nomination.

Classical scalar morphology transitions and logarithmic droplet/contact laws are credited in [literature.md](../sources/i346_ball_slab_crossover_research/literature.md). The bounded current primary-source screen does not demonstrate worldwide priority. No rate of L1 convergence, topology theorem for arbitrary near-minimizers, finite-epsilon unique transition, second-order expansion at lambda=3, dynamics, or functional Gamma-limit is claimed. There is no unresolved leading-order estimate in the proof as written; independent proof checking remains for the parent if desired.
