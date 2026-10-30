# Structural210 independent contribution review, round 1

**Conditional contribution verdict: TECHNICAL, at the entire unchanged frozen statement AND submitted proof. Correctness: UNDISCHARGED.**

The condition is full correctness of both `FROZEN-STATEMENT.md` (SHA256 `cd65e255f9fdb798bb38fd5e3291f2f657e7dae91c0af62fdf366e05ec075295`) and `AUTHOR-PROOF.md` (SHA256 `f50ea4216bce7ad43d5a713dcc7fc180ad283ff22cb9dae14a0f1d26e4a24b24`), in their entirety and byte-for-byte unchanged. It is not correctness of selected lemmas, a repaired argument, or another statement. This review neither adopts nor infers a correctness grade. The separate correctness review and its status were not inspected. Parent alone may adopt a contribution verdict or discharge its correctness condition. There is no acceptance or count decision here.

The scope assessed is exactly the smooth local immersion definition on D=(-1,1)^2: every relatively closed nowhere-dense C is the entire bad locus, with (1/2)I<=g<=2I, curvature flat to every order on C, only regular curvature zeros on D\C, and the full Euclidean metric jet at 0 when 0 belongs to C; conversely every smooth positive surface metric has a relatively closed nowhere-dense bad locus. Both directions and all additional conclusions are included. No finite-regularity replacement or unproved transfer is used.

The submission identifies a useful construction: quantify the negative-disk boundary argument for a bounded smooth immersion class, replace boundary accumulation by finitely many oriented patches, and choose a nonzero collar slope after their scales. That operation does remove the extra potentially bad loci of the literal Source334 assembly. Nevertheless, after paying the entire source patch theorem, the original cofactor calculation, ordinary finite nets, independent small parameters and diagonal summation, it is a compatible technical composition. Sections below carry that composition through the reverse inclusion and every frozen side condition. The conclusion does not rest on a failed fixed-slope attempt, a bare appeal to compactness, or a claim that the source germ already has this exact bad locus.

## 1. Source334 paid in its full operative scope

All twelve blobs in the canonical Source334 folder were checked against the complete 13,223-entry pinned tree, not a truncated listing. All operative text was read: main, model, caps, pulse, assembly, four figures and bibliography. Pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` and its operative proofs are stipulated true; this review checks their application and credits their operations without reopening their truth.

The source fixes S=[-3,3]^2, P=[-1/10,1/10]^2 and a smooth even h, with h=1 for |y|<=1/2, h>0 for |y|<1, h<0 for |y|>1, and h'(1)<0. For **any fixed smooth positive background** near S satisfying

    K_g0 = kappa (x^2-h(y)),  kappa>0,

Proposition `prop:patch` gives a residual set in the space of central supported perturbations whose metrics have no smooth height z on a neighborhood of S satisfying, throughout S,

    det Hess_g z = K_g det(g)(1-|dz|_g^2),
    1-|dz|_g^2 > 0,  H_yy != 0,  |H_xy/H_yy| <= 1/100.

The perturbations can be arbitrarily small in any specified finite collection of C^m seminorms, keep the metric positive, and keep K<-kappa/2 on [-1/5,1/5]^2. This is stronger than an isolated nonimmersible germ. The source itself explicitly observes that every zero in its whole model square remains clean: outside the central negative region the gradient is kappa(2x,-h'(y)), and its possible zeros on K=0 are excluded by h'(1)!=0. Local pointwise smooth realization therefore already coexists with the source's whole-square admissible-height obstruction.

The following analytic work is fully credited to the source, including its dependence restrictions.

* The height identity follows from H=nu II and |dz|_g^2+nu^2=1. With q=H_xy/H_yy and D=partial_x-q partial_y, the flow x=t, y_t=-q, y(0,s)=s has |y-s|<=1/50 and positive controlled y_s. Under fixed smooth C^8 bounds, positivity and lower bounds on E and |H_yy|, the cap calculation gives Dq-P_zx q-P_zy=K_y G+O(K), G=E/H_yy^2.
* Differentiating in the original coordinates before changing charts yields u_tt+A u_ss+B u_t+C u_s=R_l for u=partial_y^l z, l>=8, with A=G s_y^2 K and C=(l+1)A_s+O_l(A). The product estimates put at most one high-order factor in L2. No high chart derivative is assumed to close the induction.
* At the free cap edge, d=b-s and p=8. The directed multiplier uses W=d^p exp(-lambda s+integral B), m=-W and n=epsilon tW. The positive zero-set contribution is a controlled multiple of -K_y+epsilon t^2. Choices are epsilon, then lambda, then c1 in K<=c1d. The complementary test -d^(p-2) chi^2 phi(K/d)^2 u gives the d^(p-1)-weighted elliptic gradient estimate; its residual integrability cost is O(1+d^(p-5)). Thus the artificial edge needs no uniformly prescribed high-order data. The induction recovers mixed derivatives from the equation and closes every order.
* In `pulse`, countably many smooth C^8 height classes also impose lower Hessian/E bounds and rational q0 approximation. The shear theta=y+q0x gives a uniformly hyperbolic central slab for that fixed class. With v*=sqrt(kappa/2)M^(-3/2), L=100(1+v*^(-1)), the speed estimate is less than L/4. Cap estimates and moving-interval energy inequalities transport all tangential orders to both pulse edges.
* A change only in g_theta,theta of size tau^(-N) chi(xi) phi(tau theta/delta) cos(tau xi) has principal curvature-density contribution -1/2 partial_xi^2(delta g_theta,theta). A finite time Taylor comparison for the fixed metric gives zero initial data for the difference. Its first-derivative energy is O(delta tau^(1-N)); one spatial integration by parts over a strip of width 2delta/tau costs O(delta^2 tau^(1-N)), while the forcing moment is bounded below by c delta tau^(1-N). Endpoint moments are negligible by their all-order tangential control. Fix the class, neighborhood, metric, slab and N first; delta next; frequency last. Baire removes the bounded smooth height classes within the fixed-exterior slice.
* `assembly` already prescribes curvature through f_XX=-K0 f, rotates and dilates actual pullbacks, pays the pushforward tensor cost lambda^(-m-2), chooses arbitrary finite seminorm smallness on each patch, and sums derivative tails. It already has a finite orientation net, patches approaching every boundary point of each negative disk, disks approaching 0, and the exact Euclidean jet argument at 0.

All constants in the patch proof may depend on the fixed positive background, kappa and derivative order. The comparison below requires no uniform estimate as kappa or the patch scale tends to zero. That absence of a uniformity requirement is decisive: tiny collar slopes and tiny model amplitudes remain allowed after the geometry has been selected.

## 2. What the actual primary arguments do and do not supply

### NY2002v1

The actual 14-page [arXiv:math/0208127v1](https://arxiv.org/pdf/math/0208127v1), dated 16 August 2002, was read throughout, including Sections 2 and 3. It states a smooth K<=0/no-C3 counterexample and, separately, a smooth example with curvature strictly negative except at the origin and no C^(3,alpha) local embedding. These stronger claims are not silently treated as the later published result.

Section 2 constructs a harmonic-function/minimal-tree shortening, then a small conformal deformation preserving the length inequality. Lemmas 2.3 and 2.4 use a Legendre/ruling representation to extend a nearly rank-one flat graph as a concave flat graph and compare the saddle graph with it. A fixed 360-direction arrangement, shrinking scales and sufficiently small amplitudes force the second fundamental form to vanish at the relevant accumulation point. The final construction puts negative disks near 0, installs the oriented constructions along boundary-approaching tails, and obtains a contradiction from a graph with negative Hessian determinant inside a disk but zero Hessian on its boundary. Boundary gradient constancy makes the boundary value affine; subtracting it and taking an interior extremum gives the contradiction.

This is the actual negative-disk detection and orientation/accumulation antecedent. Its final disk argument is qualitative, not the specific numerical `ar/1000` estimate in r210. The quantitative estimate in Section 4 below comes directly from Khuri's actual flux identity plus bounded norms. It would be inaccurate either to withhold credit for NY's boundary mechanism or to attribute r210's exact constants to a displayed NY formula that is not there.

Section 3 defines an embedding norm as the infimum of the C^(1,alpha) norm of II over C^(3,alpha) embeddings. It plants obstructed metrics in annuli A_n and uses positive smooth radial tails with rapidly small coefficients. Its recursive eta_k choices retain lower bounds on the first k annular embedding norms while allowing later coefficients to become smaller. The final norm on A_m is at least m. This is already the bounded-class/diagonal strategy and a positive-background perturbation idea.

The regularity match in that proposed compactness step matters. With suitable rigid normalization, metric bounds control first derivatives of F; Gauss and Weingarten express subsequent derivatives through g and II. Uniform C^(1,alpha) control of II supplies compactness strong enough for a C3 limiting map on compact subdomains. Its underlying claimed obstruction is no C3 embedding. Source334, however, only excludes smooth heights/immersions. A bounded finite-order sequence can have a finite-order limit without a smooth one. Thus NY's compactness implication cannot simply be transplanted to Source334. The direct finite construction below does not do so.

### Published NY2008

The complete five-page [published paper, pp. 319-323](https://sites.math.washington.edu/~yuan/papers/2008CVPDE.pdf), was read. The actual Theorem 1.1 produces a C^(2,1) metric with K>=0 and no C2 local embedding. Its introduction expressly leaves the arbitrary smooth-metric question open. That difference from NY2002 remains unresolved here and supplies no novelty credit.

Its proof pays a concrete independent-parameter pattern: keep the effective radial core, attach a harmonic tail, choose its large boundary datum to arrange derivative signs, and choose the smoothing width small after the radius and tail are fixed so that the Laplacian sign survives the transition. Amplitudes of disjoint strips then tend to zero fast enough. The contradiction uses a flat generator of length 2c, b=10c^2/a, an estimate h11(t*,b)<=(M-m)b^2/c^2 and K(P)>=eta(k)c^2/a^2. Hence h22(t*,b)>=eta(k)/(100(M-m)); continuity of the C2 graph Hessian makes M-m tend to zero for fixed k. This is an actual bounded-oscillation operation, but its metric core has only C^(2,1) regularity. It is not a smooth endpoint, nor a theorem producing arbitrary exact smooth bad loci.

### Khuri2007 and Khuri2009

The [2007 paper, pp. 665-674](https://www.math.stonybrook.edu/~khuri/Khuri_Comm_PDE.pdf), was read in full extraction with the key formulas checked visually. It makes jet-dependent coefficients in a general Monge-Ampere equation, uses accumulating squares, the Legendre coordinates alpha=x-p1, beta=u_y, then another solution-dependent coordinate, and adjoint test functions exp(eta) sum tau_k^(-i)a_i b_i(tau_k s). Transport recurrences cancel leading adjoint terms. Frequency choices force an integral inequality with k^(-2)exp(-m_k^(-2)) against exp(-k^4). The smooth coefficients depend on u and its first jet. That freedom is not the freedom of one surface metric and is not credited as a metric counterexample. Source334 pays the metric-level analytic bridge instead.

The [2009 paper, pp. 451-456](https://www.math.stonybrook.edu/~khuri/Khuri_AIMS_Darboux.pdf), was read completely. Its Theorem 1 starts with a C5 Darboux solution, obtains C3 solution-dependent coordinates and a C2 solution of u_tt+K u_ss=Kf with f>0 near an appropriate boundary point. It expressly leaves construction of a suitable nonsolvable profile open. Neither that reduction nor its appendix improves arbitrary finite-regularity solutions to smooth ones.

What is directly available is the exact cofactor calculation (6)-(8) and the scalar ODE on p. 453. For H=Hess_g z, let

    T^{ij}=(tr_g H)g^{ij}-g^{ia}H_ab g^{bj}.

Then nabla_i T^{ij}=-K z^j and

    div_g(T dz) = K(2-3|dz|_g^2)

for an actual immersion height. This identity supplies quantitative boundary detection simply by estimating its boundary integral. The metric prescription is f_XX+Kf=0 with f(0,Y)=1, f_X(0,Y)=0 and g=dX^2+f^2dY^2. Both are fully paid operations.

### Actual smooth clean-zero existence interface

The [Keio original report KSTS/RR-86/011, 22 October 1986](https://www.math.keio.ac.jp/wp-content/uploads/2022/03/86011.pdf), was visually read in the relevant statements and proof, not inferred from NY's bibliography. Theorem A states smooth local embedding for a smooth Riemannian surface at a point of nonzero Gaussian curvature. Theorem C, spanning printed pp. 2-3, states local C-infinity embedding of a neighborhood of p0 into R3 when K(p0)=0 and dK(p0)!=0. The surface/metric is in the smooth setting. These are pointwise existence assertions for new maps on some neighborhoods, precisely the interface required here.

The two-dimensional calculation on printed p. 8 uses K as a coordinate and the normalized model symbol q=-(xi1^2+x1 xi2^2). At its degenerate characteristic x1=xi1=0, xi2!=0, the base differential has a nonzero dx1 term and is independent of the canonical covector direction. This is real principal type in the stated sense, even when the fiber gradient vanishes. The preprint's theorem-letter references in this part are inconsistent; the displayed hypotheses and calculation identify the clean-zero case.

Section 2 constructs an approximate embedding to a prescribed finite metric-jet order. Section 3 proves the nonlinear existence theorem with a right inverse losing a fixed number d of derivatives but obeying a tame estimate of the form

    ||v||_(s-d) <= C_s (||h||_s + ||u||_s ||h||_d).

Its smoothed iteration uses theta_n=theta^(tau^(n+n0)), tau=4/3. The residual decays in a low norm, high norms have controlled growth, and interpolation makes the same sequence converge in every Sobolev order. Section 4 applies this to the metric problem. The appendix constructs stable local contact/canonical coordinates from the Hamiltonian flow, reduces the operator by Fourier integral operators, forms a finite microlocal parametrix, and corrects the remainder with (I-K(u))^(-1) when its L2 norm is at most 1/2. This establishes the existence interface being invoked; it is not the impermissible assertion that an arbitrary C3 compactness limit is smooth. Earlier Fourier-integral references used by that paper were not recursively audited.

The exact 1989 AMS endpoint was independently retried and returned HTTP 403. No identity of the 1986 report with the 51-page 1989 publication is claimed. The actual accessible report supplies the read theorem; the failed endpoint is an access/version limit, not evidence of novelty or a new r210 regularity operation.

## 3. Original project overlap and the limits of clearance

The three pre-admitted r22 sections were independently binary-seek read from the exact original `candidate.md`, without adjacent sections or a directory inventory, and checked against the exact packet copies:

* [1520,3282): both realizable and nonrealizable metrics are dense in the flat-jet metric space. The operative estimate is ||chi_rho f||_Cm<=C rho^(N-m) for f flat, with N>m. This already credits flat-jet cutoff smallness and finite-seminorm/diagonal thinking; it does not supply ambient residuality.
* [3282,4123): B(g) is relatively closed, B(g) is contained in {K=0}, and an open bad set would be locally flat and hence locally planar. The entire necessity direction of the current frozen statement is already this original deduction.
* [4123,6482): exact prescribed loci and full ambient genericity are explicitly research questions, not frozen assertions. The note correctly identifies the reverse-inclusion problem at the source's flat disk boundaries and warns against upgrading a finite-regularity compactness limit. Those questions/warnings alone are not substantial mathematical results. They receive credit for identifying the actual interface, not for proving the current realization theorem.

One new focused search, narrower than the author's older search, used precise finite-net, negative-disk/cofactor, independent-mass/collar and Darboux bounded-class/diagonal compounds under all 343 wildcard/no-r guards, 162 full-path substrings, component predicates and prospective administrative-heading rejection. The r22 namespace was additionally excluded from this traversal, since only its admitted ranges may be read. It navigated 1,647 eligible UTF8 files without extension/size/hidden/ignored cutoffs; no other original mathematical section was admitted. One prospective r13 section matched only “negative disk”; the query was restricted to nearby curvature/Gauss/Darboux/isometric terms before body display, and the candidate failed. Its body was not displayed or used. No broader rerun followed.

This is not exhaustive clearance. Coarse guards deliberately omit eligible-looking material, and opaque aliases can defeat filename classification. No excluded author, peer, parent, closed or active namespace was read. There is no world-priority inference from search silence.

## 4. Direct quantitative finite replacement, with constants

The following is the strongest compatible construction after the paid interfaces. It instantiates the choices permitted by the unchanged submitted proof; it neither alters that proof nor narrows its scope. It is a contribution comparison, not an independent correctness certificate for the entire submission.

Fix a ball B(c,4r) compactly inside D, M>=1, r<=1/(1000M), a in (0,1], and a smooth metric there with I/2<=g<=2I. Suppose K<0 in Delta=B(c,r), K=0 on its circle, and K=-a on B(c,r/2). Consider a smooth isometric immersion on a neighborhood of the closed ball with coordinate second and third derivatives of Euclidean length at most M.

Put n=(F_X cross F_Y)/|F_X cross F_Y|, e=n(c), z=<F,e>, nu=<n,e>, H=Hess_g z=nu II. Isometry gives |F_X|,|F_Y|<=sqrt(2) and |F_X cross F_Y|=sqrt(det g)>=1/2. Differentiating the normalized cross product gives |partial_i n|<=4sqrt(2)M<6M, hence

    |n(x)-n(c)| <= 9M |x-c| <= 36Mr <= 0.036.

Thus nu>0 and |dz|_g<=1/2 everywhere needed. Since |II_ij|<=M,

    |partial_k H_ij| <= M+12M^2 <= 13M^2,
    ||H(x)-H(y)||op <= 100M^2 |x-y|.                  (4.1)

This estimate comes from F and metric eigenvalues, not from uniform high derivatives of the chosen metric.

Integrate Khuri's cofactor identity over Delta. Because 2-3|dz|_g^2>=1 and sqrt(det g)>=1/2, the magnitude of the negative integral is at least pi a r^2/8. If H*=max_boundary ||H||op, then ||T||op<=12H*: indeed |tr_g H|<=4H*, ||g^(-1)||<=2 and ||g^(-1)H g^(-1)||<=4H*. The Euclidean lengths of dz and the g-unit conormal are at most sqrt(2)/2 and sqrt(2); the circle's g-length is below 9r. Consequently

    pi a r^2/8 <= 108 r H*,
    H* >= pi a r/864 > ar/1000 =: h0.                (4.2)

At a maximizing point b, H is nonzero rank one: nu>0, K=0, and the Gauss equation make det H=0. There is no solution-dependent rotation of a scalar PDE here; z is an actual component of the single hypothetical F in the fixed ambient direction e.

Set sigma=h0/(10^6 M^2). Take a fixed finite net of unoriented first-axis lines of angular mesh at most 10^(-3), and a finite sigma/10-net b_i on the disk circle. For each pair of a circle-net point and a direction, choose a distinct center strictly outside the closed disk within sigma/3 of b_i. Each choice is in an open nonempty set and only finitely many choices are made. After all centers are fixed, choose positive scales lambda_p small enough that their rotated [-4,4]^2 images have disjoint closures, avoid the disk, lie in its width-r/10 collar and B(c,2r), and stay within sigma/2 of their b_i. Positive minima of finitely many separations, distances to forbidden closed sets and sigma give these scales. No slope or model amplitude has yet been chosen.

Choose i near b and the direction whose first axis is within 10^(-3) of ker H(b). In this frame

    |H_yy(b)| >= H* cos^2(10^(-3)),
    |H_xy(b)| <= H* |sin(10^(-3))cos(10^(-3))|.

All points of the selected full patch are within sigma of b. By (4.1), the matrix error is at most h0/10^4<=H*/10^4. The diagonal remains at least (cos^2(10^(-3))-10^(-4))H*>0, and the mixed/diagonal ratio is less than 0.0012<0.01. The gradient condition also persists. Under Phi_p(x)=c_p+lambda_p R_p x the Hessian is lambda_p^2 R_p^T H R_p and the gradient norm is intrinsic. The common scalar factor does not affect the ratio. A Source334-obstructed pullback therefore excludes every smooth immersion in this bounded class on the entire ball.

This is finite capture, with explicit strict margins. It is an elementary quantitative use of the paid flux identity, ordinary differentiation and two compact finite nets. It takes no compactness limit. In particular, it does not assert that a C3 height is ruled out by the source, or that this finite block has an individually bad point. The outer bound M controls only this continuity argument. No C8 bound on the pulled-back height is deduced from it: the already-paid source patch theorem has removed all of its own bounded smooth C8 classes and excludes every smooth admissible height, however large its higher derivatives.

## 5. Independent collar slope pays the entire finite geometry

Fix m, a budget epsilon>0 and a smooth outer cutoff beta equal to 1 on B(c,2r), zero outside B(c,3r). Let T>=1 bound multiplication by beta in C^m. All norms below include orders <=m and fixed component conversions.

For rho=|x-c| construct a radial family k_(a,b), 0<b<=a/r, with

    k_(a,b)=-a                for rho<=r/2,
    k_(a,b)=b(rho-r)          for 0.9r<=rho<=1.1r,
    k_(a,b)=a                 for rho>=1.5r.

Use fixed smooth cutoff fractions to blend -a with b(rho-r) between r/2 and 0.9r, and b(rho-r) with a between 1.1r and 1.5r. Both inputs have the same strict sign in their respective blends. The function is constant near c. For a fixed m and r there is a finite C_m(r), bounded by a fixed multiple of max(1,r^(-m)), such that

    ||k_(a,b)||_Cm <= C_m(r) a,  uniformly for 0<b<=a/r.   (5.1)

Choose a>0, a<=1, so that T C_m(r)a<epsilon/4. **Now** choose the nets, centers and scales in Section 4, using this fixed a in h0 and sigma. These finite scales may be extremely small; they will not require a later reduction in a.

Let chi_p equal 1 on a neighborhood of S and be supported inside (-4,4)^2. In the physical patch replace k_(a,b) by

    (1-chi_p^phys) k_(a,b) + chi_p^phys kappa_p m_p,
    m_p = (x^2-h(y)) composed with Phi_p^(-1).        (5.2)

The model is strictly positive wherever chi_p transitions, since that transition is outside S. The old curvature there is b(rho-r)>0. Thus this interpolation creates no zero. Within S the model zeros are regular, and all full patches stay a positive distance from the disk circle.

There is no implicit infinite family of inequalities inside one block. For N patches define the finite, geometry-dependent constants

    C_p = max_(|alpha|<=m) ||D^alpha[chi_p^phys(rho-r)]||infinity,
    D_p = max_(|alpha|<=m) ||D^alpha[chi_p^phys m_p]||infinity.

Because the entire patch support lies in the linear collar, its correction has C^m norm at most C_p b+D_p kappa_p. Derivatives of chi_p and m_p include all powers of lambda_p^(-1); those costs are already inside C_p,D_p, fixed before b or kappa_p. For example choose

    0<b<min(a/r, epsilon/[16T(1+sum_p C_p)]),
    0<kappa_p<epsilon/[16TN(1+D_p)].                 (5.3)

Then the sum of correction norms is less than epsilon/(8T). Together with (5.1), this gives ||beta k||_Cm<epsilon/2. The disk retains K=-a in its core and negative curvature throughout its interior; its boundary slope is exactly b>0. The model patches retain their exact scalar curvature profiles. Every zero in the block is either the clean disk circle or a clean model curve; all intervening blends are positive.

Thus the complete order is

    r,M,m,epsilon,beta,T -> a -> h0,sigma,nets,centers,scales
       -> b>0 -> kappa_p>0 -> later metric perturbations.

The signal controlling capture is a, while every costly tiny-scale correction is proportional to b or kappa_p. There is no lower bound on b or kappa_p other than strict positivity. This is a triangular finite choice of independent small parameters, not a new coupled analytic estimate. A fixed choice b comparable to a/r can fail high-derivative budgets; that failure says nothing against (5.3). Conversely, merely saying “two scales” would not suffice without (5.1)-(5.3) and the sign checks.

## 6. Arbitrary relatively closed nowhere-dense C, including all accumulations

Let C be nonempty and E=D\C. Schedule a countable basis of balls compactly inside D that meet C, each infinitely often. At stage n the finitely many previously chosen closed blocks avoid C. Near a point of C in the scheduled basis ball choose c_n in E, avoiding all previous blocks, with dist(c_n,C)<2^(-n). Choose r_n>0 so that the closed B_n=B(c_n,4r_n) stays in E and that basis ball, avoids all previous closed blocks, and

    r_n<min(2^(-n),1/[1000(n+1)]),
    4r_n<dist(c_n,C)/2.

Every p in C is approached by a subsequence of centers with indices tending to infinity. All points of B_n have distance from C tending to zero. A compact subset of E has positive distance from C, so it meets only finitely many blocks. This proves local finiteness on all of E; C may be uncountable or have positive measure.

On block n use Sections 4-5 with M_n=n+1, m=n and epsilon_n=2^(-n-20), obtaining beta_n,k_n and its finitely many patches. Put gamma_n=epsilon_n/(2T_n), where T_n bounds multiplication by beta_n in C^n. A positive flat background can be built directly; no theorem with unverified hypotheses is needed.

Choose nonnegative compactly supported smooth bumps phi_j in E whose positive sets cover E. Each support meets only finitely many B_n. Choose t_j>0 satisfying the finite requirements

    ||t_j phi_j||_Cl <= 2^(-j-20)    for l<=j,
    ||t_j phi_j||_Cl <= 2^(-j)gamma_n
        for l<=n and every B_n meeting supp(phi_j).

This is possible even if those finitely many n are large. For each fixed derivative order, the tail is uniformly summable; the remaining finitely many terms are smooth. Extend the bumps by zero and set k_+=sum_j t_j phi_j. Then k_+ is smooth, positive everywhere on E, has every derivative zero on C, and obeys

    ||k_+||infinity<=2^(-20),
    ||k_+||_Cn(B_n)<=gamma_n.

Flatness follows by evaluating each uniformly convergent derivative series at a point of C: every summand is zero on a neighborhood of that point. No distance-to-C estimate is omitted or needed in addition to this all-order uniform convergence.

Now set

    K0=k_+ + sum_n beta_n(k_n-k_+).                  (6.1)

The n-th correction has C^n norm below epsilon_n. The same tail argument proves smoothness across **every** point of C and all other accumulations, and all curvature jets vanish on C. Also ||K0||infinity<2^(-19)<10^(-3). In the beta_n transition, k_n=a_n>0 and k_+>0; their convex combination is positive. Outside the blocks the curvature is k_+>0. Since each block has finitely many patches and the blocks are locally finite on E, no extra unexamined zero or accumulation locus remains there. The only E-zeros of K0 are the regular disk circles and model curves.

This is Source334's all-order summation operation with a countable-basis placement and a positive flat background. The construction of that background is explicitly included so that no general original theorem is being invoked under unspecified hypotheses.

## 7. One metric: bounds, preserved patches, exact zeros and jets

Solve globally on D, with Y a parameter,

    f_XX=-K0 f,  f(0,Y)=1,  f_X(0,Y)=0,
    gbar=dX^2+f^2 dY^2.

The integral equation on each segment from 0 to X gives sup|f-1|<=10^(-3)sup|f|. Thus sup|f|<=1/(1-10^(-3)), |f-1|<0.002, f>0, and K_gbar=-f_XX/f=K0. Smooth ODE dependence supplies all mixed derivatives. There is no compact-support assertion for this background metric; its nonlocal dependence in X is allowed by the frozen statement.

Enumerate the finitely many patches in each block as p=1,2,... . On each actual pullback g0,p=Phi_p^*gbar, curvature is the scalar K0 composed with Phi_p, exactly kappa_p(x^2-h(y)) near S. The coefficient factor lambda_p^2 in the pullback is not a curvature-amplitude factor. Apply Source334 separately to this fixed positive background and kappa_p. Choose a supported perturbation eta_p excluding every smooth admissible height while keeping its central box strictly negatively curved. Pay the physical-coordinate norms by the actual formula

    eta_hat_p=lambda_p^(-2)R_p(eta_p composed with Phi_p^(-1))R_p^T,
    ||D^m eta_hat_p||<=C_m lambda_p^(-m-2)||D^m eta_p||.

Demand ||eta_hat_p||_Cm<=2^(-p-10) for m<=p, with all norm conversion constants included. Only finitely many seminorms are demanded of the source at any one application. Then

    g=gbar+sum_p eta_hat_p                               (7.1)

is smooth, including across C. The total operator-norm perturbation can be below 1/8; with |f-1|<0.002 this leaves (1/2)I<=g<=2I everywhere. Every patch obstruction survives exactly because all other tensor supports miss that full patch.

For each fixed disk there are only finitely many patches in its block, separated from its closed disk, and all other blocks are disjoint from its closed block. The tensor sum therefore vanishes on a neighborhood of that disk. Its negative curvature, core mass and boundary circle are preserved. Curvature changes only inside model central boxes already strictly negative; the source keeps those boxes negative. Consequently the entire zero set is exactly

    K_g^(-1)(0)=K0^(-1)(0)
      = C union {disk circles} union {physical model zero curves}.   (7.2)

This is an exact set equality, not just a sign argument at selected points. At every zero q in E, a neighborhood is unaffected by the tensor perturbations, so dK_g(q)!=0. The local finiteness established above rules out an omitted E-accumulation point.

Every derivative of the tensor sum vanishes on C by uniform derivative-tail convergence. Curvature and any derivative of curvature are smooth finite-jet expressions in a positive metric. At each p in C, their jets therefore agree with the corresponding jets for gbar, whose curvature is K0. All partial^alpha K_g(p) vanish.

If 0 belongs to C, the ODE data give partial_X^a partial_Y^b(f-1)(0)=0 for a=0,1. For a>=2,

    partial_X^a partial_Y^b(f-1)(0)
       =-partial_X^(a-2)partial_Y^b(K0 f)(0)=0,

because every Leibniz term contains a derivative of K0 at 0. Thus gbar-I is flat at 0, and the flat tensor sum preserves that full metric jet. No Euclidean metric-jet claim at other points of C is made or used.

## 8. Exact locus, empty set and the full converse

Fix p in C and assume a smooth immersion on some neighborhood U. Restrict to a closed coordinate ball about p compactly inside U. Its second and third derivatives have a finite bound M. Infinitely many chosen centers tend to p with n tending to infinity; since r_n tends to zero, eventually their entire B_n lies in that ball and M_n=n+1>=M. The finite net selected for exactly a_n,r_n,M_n captures the corresponding height by Section 4. Its selected full patch is source-obstructed by Section 7, a contradiction. Hence C is contained in B(g).

For the reverse inclusion, fix **any** q in E. If K_g(q)!=0, the actual smooth nonzero-curvature theorem applies to this positive C-infinity metric. If K_g(q)=0, (7.2) and its regularity prove dK_g(q)!=0, so the actual smooth clean-zero theorem applies. Thus q has a smooth local immersion in either case. This includes every disk circle, every model curve, all cutoff boundaries, all gaps and every other complementary point. The local maps need not glue or extend across a whole block. Therefore B(g) is contained in C and B(g)=C.

For C empty, choose 0<epsilon<=1/16 and g=dX^2+cos^2(sqrt(epsilon)X)dY^2. Its curvature is the positive constant epsilon and its eigenvalues lie between cos^2(1/4)>1/2 and 1. Nonzero-curvature smooth existence gives B(g) empty. All other frozen conditions are vacuous in this case.

For any smooth positive metric, without the uniform coefficient bounds, D\B(g) is open by its defining neighborhood quantifier. Nonzero-curvature existence puts B(g) inside {K=0}. If a nonempty open V were contained in B(g), then K would vanish throughout V. Locally choose an oriented orthonormal coframe. Its connection form is closed; on a small simply connected neighborhood integrate that form, rotate the coframe to make the connection zero, and integrate the resulting closed coframe as du,dv. The map (u,v,0) is a smooth isometric immersion there, a contradiction. Hence B(g) is relatively closed with empty interior, and therefore nowhere dense. This is exactly the already-admitted r22 necessity argument, with its elementary flat realization written out.

Sections 4-8 pay every requested conclusion in one compatible construction. No residuality in the full metric space, stability of a smooth obstruction under arbitrary perturbations, finite-order nonsolvability transfer, limit regularity improvement or genericity claim has entered.

## 9. Contribution assessment, objections and unresolved limits

The reason for TECHNICAL is specific to the full paid interface, not the apparent shortness of the result or a blanket rule that quantitative statements are routine. The source has already supplied the difficult analytic operation: arbitrarily small metric perturbations on a fixed full patch, with clean zeros and fixed exterior, forbidding every admissible smooth height. Once that is available:

1. The only new boundary estimate is the absolute-value bound on the already-derived cofactor flux (4.2); its explicit constants have been carried above.
2. A known C3 bound on a hypothetical **smooth** immersion gives the explicit modulus (4.1). Finite covering of a compact circle and the compact space of directions then replaces the source's internal infinite accumulation.
3. The small-slope issue is resolved by the independent positive variables in (5.3). The derivative costs do not constrain the previously fixed mass. No new estimate is required of the cap theorem or the pulse as these parameters decrease.
4. The zero-set accounting and positive background (6.1)-(7.2) put every complementary point within the exact classical existence interface. Countable placement and all-order summation then move the remaining accumulation set to arbitrary C.

This is more than literal insertion of disjoint copies of the source germ, and the submission deserves credit for recognizing and implementing the compatible finite replacement. But it leaves no demonstrated substantial nonroutine operation after the strongest source/classical construction. The finite-net, independent-parameter and diagonal substitution is sufficient at the **entire** frozen scope. This review does not claim an earlier published theorem already states the same classification.

The following possible objections were considered rather than silently discarded.

* Direct insertion of the original source assembly leaves flat disk boundaries whose local realizability is unproved. Resolution here is actual finite capture and b>0, plus the complete positivity and zero-set accounting, not an assumption about those old boundaries.
* A fixed-slope profile can lose small C^m norms at tiny patch scales. Resolution is the explicit triangular choice (5.3); it preserves both the capture mass and every clean zero. That failed naive construction is not evidence for substantiality.
* NY2002's bounded-norm argument uses the regularity of its own claimed obstruction. It does not authorize smooth nonsolvability transfer for Source334. The finite argument uses no limit at all.
* Khuri2007's freely jet-dependent coefficients do not furnish a metric. The source's actual metric pulse theorem is the dependency that supplies the metric-compatible analytic obstruction.
* The source patch constants need not be uniform across this construction. Each application is to a fixed positive background after all its scales and kappa have been selected; only finitely many seminorms are then requested.
* Curvature-flat jets at arbitrary C do not imply Euclidean metric jets there under the global horizontal ODE. The only metric-jet claim used is the unchanged conditional assertion at 0, proved from that ODE's initial line.
* The NM86 report contains inconsistent theorem-letter references and uses prior Fourier-integral results in its parametrix. The actual smooth Theorem A/C hypotheses, the two-dimensional clean-zero symbol, and the nonlinear construction were read. The inaccessible 1989 version was not silently substituted. No assertion about arbitrary finite-regularity maps follows from the read interface.

There is no essential unresolved **contribution comparison** after this direct construction and these precise paid dependencies. This statement does not discharge the correctness condition on either immutable submitted artifact. No independent correctness certification is supplied by the mathematical comparison, by hashes, by author checks or by the artifact verifier.

Project novelty, substantial contribution and demonstrated new-to-literature priority are distinct. Relative to the three admitted r22 sections this is a realized exact-locus construction in the submission, whereas r22 posed the sufficiency as a question. That may distinguish the submitted project formulation. It does not establish substantiality under the campaign criterion, and bounded primary/history access cannot establish new-to-literature priority. Neither a prior published exact classification nor worldwide originality is claimed.

The authenticated Lean comparator proves a coordinate-square openness lemma but its endpoint `exists_local_metric_without_local_immersion` ends in `sorry`. It supplies no completed formal endpoint support, and no compilation or downstream formalization was performed.

**Handoff remains: TECHNICAL conditional on full correctness of the ENTIRE unchanged frozen statement AND submitted proof; correctness UNDISCHARGED; parent alone adopts. No acceptance/count.**
