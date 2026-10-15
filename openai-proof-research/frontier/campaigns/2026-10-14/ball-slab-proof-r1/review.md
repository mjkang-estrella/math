# Independent proof review: second-order unrestricted ball–slab contact

2026-10-14. **Verdict: PASS for the full stated scope, without necessary repair.** This is a proof verdict only. It neither establishes substantial contribution nor changes acceptance, priority, or publication status.

The reviewed frozen candidate has SHA256
`30bb73d2601754dcc6aa9eb26537e083256849acd3b5cf94a710970dfe067e54`.
I read it completely and independently checked its new deductions and the needed local antecedents. Earlier PASS or TECHNICAL labels were not premises.

## Exact scope passed

On the unit cubic flat T3, the original admissible class is every finite-perimeter pair E subset F a.e., with |E|=4pi R^3/3 and |F|=2(R-epsilon). The deficit is P(E)+P(F)-4pi R^2-2. The additional ball-neighborhood constraint is used only in the auxiliary exact minimum M_B; it is not imposed on the original global class.

Uniformly as R<1/3 tends to 1/3 and epsilon decreases to zero, with no relation between their rates, the proof establishes

    M_B = 2pi epsilon^2/(ell+log ell) + O(epsilon^2/ell^2),
    ell=|log epsilon|.

The independently rechecked local antecedents give, eventually and exactly,

    L_R(epsilon)=min{M_B(R,epsilon),g(R)},
    g(R)=2pi sqrt(4R^3/3)-4pi R^2.

Hence, writing S=epsilon^2/ell, T2=epsilon^2 log(ell)/ell^2 and delta=1/3-R, the claimed crossover limit is

    (L_R(epsilon)-2pi S)/T2 -> min{-2pi,(2pi/3)alpha}

whenever (delta-3S)/T2 tends to a finite real alpha. No smooth, radial, graph, connectedness, or fixed-topology assumption is added to the original pairs. Graph regularity is derived only for exact minimizing replacements.

## Antecedent reduction checked independently

Actual pinned scalar Theorem `intro:main` gives the profile with v=min(V,1-V) and its exhaustive equality classes. At inner endpoint volume 4pi/81 the equality sets are precisely balls and shortest coordinate tubes; at outer endpoint volume 2/3 the occupied coordinate slab is the sole type, by complementation. Nearby R<=1/3 therefore gives separate nonnegative deficits P(E)-4pi R^2 and P(F)-2 for every competitor.

The endpoint inner ball and tube translation orbits are separated in L1. Along the tube's axis the tube has constant section area a_*=4pi/81. A ball projects into an interval of length 2/3, so |C minus B|>=a_*/3. Equal volumes imply |C triangle B|>=2a_*/3. Their a_*/10 closed neighborhoods are disjoint. These distance constraints are L1 closed, so the direct method gives exact localized paired minimizers. Uniform ball recovery has cost O(S), and the strictly nested tube/slab competitor costs g(R). Both tend to zero. Compactness plus the stipulated equality classification forces every local limit into its selected orbit; consequently the artificial constraint is eventually inactive. Global exact minima have the same ball-or-tube alternatives, proving reduction to the two local minima. A tube normal to a slab cannot be contained in it; a parallel tube can. A limiting ball's normal center is forced to the slab midpoint because its projection has exactly the slab width.

For the local regularity step, an inner patch strictly inside the slab and a face patch outside the inner set exist at every limit, including tube/face tangency. The two compactly supported ambient fields have an invertible diagonal two-volume derivative. Their volume maps for nearby measurable pairs are integrals of smooth Jacobians, so the inverse bound persists without any regularity of the competitors. The same ambient diffeomorphism corrects both volumes and preserves inclusion. For total volume error q it has parameter O(q), perimeter cost O(q) on bounded-perimeter sets, and L1 displacement O(q); the last follows from the usual BV transport estimate along the smooth flow.

The lattice pairs (H intersection F,H union F) and (E intersection H,E union H) have summed perimeter bounded by the scalar comparison perimeter plus the unchanged perimeter. Their summed paired symmetric difference is exactly the scalar symmetric difference. For smaller-perimeter H supported in a sufficiently small fixed ball, common volume correction preserves the inactive neighborhood and yields scalar perimeter comparison with error C|H triangle E| or C|H triangle F|. Larger-perimeter H satisfy it automatically. Larger balls satisfy the trivial uniform perimeter bound. This covers every ball and every scalar comparison in AFM Definition 2.5, not just volume-preserving or nested comparisons.

Actual AFM Theorem 4.2 gives whole-boundary normal graphs converging in C^{1,beta}, beta<1/2, under this common comparison condition, bounded perimeter, and a smooth L1 limit. It applies separately to the inner set and the disconnected two-face slab boundary. L1 convergence fixes the occupied interval and excludes the complementary-side ambiguity. Whole-boundary graphs exclude extra components of these exact replacements. Thus pointwise inclusion inequalities can be used on their regular representatives. Arbitrary original competitors are never declared graphs.

I also checked the exact cylinder branch rather than treating I346's label as evidence. Its volume equation is integral(rho u+u^2/2)=0; its area density is sqrt((rho+u)^2(1+u_s^2)+u_theta^2). Transverse centering removes k=0,m=+/-1. The constant coefficient is quadratic by exact volume. All other Jacobi eigenvalues 4pi^2 k^2+(m^2-1)/rho^2 have a uniform positive gap near rho=2/9, since min{4pi^2-81/4,243/4}>0. The exact-volume expansion and C1-smallness therefore give P(E)>=2pi rho+c||u||_H1^2 for localized replacements. With P(F)>=2 and the strictly nested exact tube competitor, M_C=g(R) exactly. No o(delta) remainder is divided by T2.

## Uniform graph control and nonlinear errors

After AFM on a normalized limit, changing reference radius from 1/3 to R subtracts a smooth small constant and rescales a smooth sphere parametrization. Changing the reference center is a uniformly invertible C^{1,beta} coordinate change: the horizontal/radial graph map has derivative close to the identity, and its inverse has bounded C^{1,beta} norm. The finite-dimensional centering equation has nonsingular translation Gram matrix. Thus AFM's C^{1,1/4} bound survives rebasing and centering. For faces, reference changes are constant height shifts and transverse translations. A contradiction sequence would admit a normalized smooth equality limit and the preceding common AFM contract, contradicting an unbounded rebased Hölder seminorm. This proves joint uniform boundedness; no unproved speed of C1 convergence is assumed.

The exact sphere volume equation bounds its mean b by C||psi||_L2^2. Its degree-one components vanish exactly. The positive l>=2 spectral gap, and the face Poincare inequalities after both face means are made zero, absorb the quadratic mean and small area remainders. The uniform O(S) upper bound therefore gives all H1 norms O(sqrt(S)) and b=O(S). The slab has exact volume 2(R-epsilon)+integral(V^++V^-); reference axial translation changes the two means oppositely. Thus both can be set to zero while retaining the relative sphere/slab axial displacement h.

For completeness, the interpolation exponent checks exactly. If a gradient with uniformly bounded beta-Hölder seminorm has maximum M, it stays at least M/2 in a chart disk of radius c M^{1/beta}; hence ||Du||_L2^2>=c M^{2+2/beta}. With beta=1/4 and ||Du||_L2=O(sqrt(S)), M=O(S^{1/10}). Connectedness and the respective mean bounds control the function supremum. This applies separately to the two connected faces and to the sphere. The small-disk argument is uniform in the compact reference family.

The exact-volume radial sphere expansion has remainder bounded by C(||psi||_infinity+||Dpsi||_infinity^2)||psi||_H1^2; the flat-face errors are quartic in gradients. Splitting psi=b+f gives Q_R(psi)=Q_R(f)+O(S^2), with f in l>=2. Consequently

    D_R = Q/2 + O(S^{11/10}+S^2),
    Q=Q_R(f)+integral|DV^+|^2+integral|DV^-|^2.

This is sufficient at the new scale: S^{11/10}/(epsilon^2/ell^2)=epsilon^{1/5}ell^{9/10}->0, and S^2/(epsilon^2/ell^2)=epsilon^2->0. No old unspecified o(S) is used at scale T2.

## Kernel normalization and the actual-curve trace passage

The unit-torus mean-zero Laplace inverse has local singularity -(1/(2pi))log distance plus a bounded continuous regular part. The cutoff-fundamental-solution construction in the candidate supplies this, including its mean-zero normalization.

On S_R, an L2-normalized degree-l spherical harmonic is R^{-1} times its unit-sphere counterpart. Dividing its rank-one kernel by the Jacobi eigenvalue [l(l+1)-2]/R^2 cancels both R factors. Therefore the kernel relative to physical area is exactly

    sum_(l>=2) (2l+1)P_l(omega dot eta)/[4pi(l(l+1)-2)].

Its difference from the mean-zero Laplace kernel, apart from removal of the finite l=1 term, has coefficients

    2(2l+1)/[4pi l(l+1)(l(l+1)-2)].

They are absolutely summable. More explicitly, after removing 1/(4pi), each is

    1/(l-1)-1/l-1/(l+1)+1/(l+2),

whose sum over l>=2 is 2/3. Since |P_l|<=1, the difference is a bounded continuous kernel with bound 1/(6pi) before the finite-rank term. The Laplace kernel is -(1/(4pi))log(1-omega dot eta) plus a constant. Its pole flux is one and its off-pole negative Laplacian is minus the reciprocal sphere area. Its local singularity in physical distance is therefore -(1/(2pi))log distance; replacing unit chord distance by physical chord adds only the uniformly bounded constant involving log R. This checks the normalization and all nontranslation low modes.

Here is a detailed justification of the candidate's compressed trace step. Fix one of its actual C1 curves and bounded parameter density, and mollify the resulting measure in surface charts at scale t<a, using positive smooth kernels. For smooth projected source measures, spectral Cauchy–Schwarz gives the dual estimate with their double inverse-kernel integral. The kernels just established have continuous bounded regular parts. For the singular part, when two original curve points are separated by more than a fixed multiple of t, mollification changes the logarithm by a bounded amount. At separation O(t), the mollified logarithm is bounded by C+log(1/t), which is dominated by C+log^+(1/distance) of the original pair. The actual curve separation is at least c a|e^{i theta}-e^{i phi}|. Thus, for this fixed a, all mollified integrands have an integrable dominating function

    C + |log(a|e^{i theta}-e^{i phi}|)|.

This proves convergence of the self integrals; distinct polar curves remain separated, so cross integrals converge directly. Smooth sources converge weakly to the curve measure. For smooth graph test functions the pairings converge. Smooth approximation in both C0 and H1, with finite-dimensional projection onto the required subspace, extends the inequality to the actual C1 graph functions. This establishes (4.4) without postulating a bounded H1 point trace. Mean and translation projections are already included in the inverse kernel; the source measures need not have zero mass.

Uniformity of the self-integral estimate comes from scaling out a before integrating the logarithm. The actual inverse horizontal parametrization is bilipschitz uniformly at scale a for every angular pair, not only for widely separated angles. Its forward map is y -> (1+psi(q(y))/R)y, with derivative uniformly close to I. Composing with the reference polar graph preserves both chord bounds. The exact multiplier satisfies A(p,0)=1 identically for all small p and is smooth in p and |x|^2, so A-1=O(a^2), with no additive C1 error in the height.

There are four self integrals: two independent mean-zero torus-face summands and two source curves in the single sphere summand. Each has leading coefficient (1/(2pi))log(1/a). The weighted spherical masses are 1+O(a^2), producing only O(a^2 log(1/a)). The two spherical cross integrals are O(1); the two faces have no cross term because their quadratic spaces are different summands. Thus

    ||Lambda_a||_*^2 <= (2/pi)log(1/a)+C.

The coefficient is 2/pi, not 1/pi. The dependence of the curves and weights on the particular minimizing graph is harmless: fix them when applying the dual inequality, then use their uniform bounds.

## Lower bound and exact drift cancellation

The actual upper and lower vertical inclusion constraints have right sides epsilon+h-q_R and epsilon-h-q_R respectively. They are evaluated on the same physical horizontal circle and are added with unit averaging coefficients. Hence h cancels identically, without any hypothesis on h/epsilon. The weights A multiply f only; they do not multiply h.

Set a=sqrt(epsilon/ell), L=log(1/a)=(ell+log ell)/2. Since q_R(a)=O(epsilon/ell) uniformly and b=O(S), their sum gives

    Lambda_a >= 2epsilon-C epsilon/ell-C S > 0.

Together with the checked dual bound,

    Q >= (2epsilon-C epsilon/ell-C S)^2/[(2/pi)L+C].

Combining with the quantified area expansion yields

    M_B >= pi epsilon^2/L-C epsilon^2/ell^2
         =2pi epsilon^2/(ell+log ell)-C epsilon^2/ell^2.

The numerator and denominator perturbations each produce at most O(epsilon^2/ell^2). All discarded nonlinear errors are smaller. The source sphere uses f with exact l=0,1 removal; no fixed relative geometric loss or growing spectral cutoff is present. Sequential contradiction and the compact normalized equality family promote these constants to joint uniformity. This proves the auxiliary minimum's lower bound over its entire original finite-perimeter localized class by exact replacement.

## Recovery, exact volumes, and the curvature error scale

The tangent profile uses a^2(H+1/2)=R epsilon, H=log(d/a), A=a^2/R. For r<=a, Z=epsilon-r^2/(2R); for a<r<d/2, Z=A log(d/r), followed by a fixed smooth nonnegative cutoff. At a both value and radial derivative match. The difference from the parabola has derivative r/R-a^2/(Rr)>=0 outside a, so the logarithmic tail lies above that obstacle. Since q_R(r)>=r^2/(2R), it also lies above epsilon-q_R(r). The cutoff acts where this latter obstacle is negative. This proves actual inclusion after moving each sphere cap inward vertically by Z/2 and its face outward by Z/2. Outside the caps the gap is positive. The resulting embedded inner region has compact vertical slices whose extrema lie on its boundary, so boundary containment implies region containment without a connected-slice hypothesis.

Direct integration, before the cutoff change, gives

    J=int|DZ|^2=2pi epsilon^2(H+1/4)/(H+1/2)^2.

The cutoff modifies J by O(A^2). Also int Z=O(A), int Z^2=O(A^2), int r^2|DZ|^2=O(A^2), and ||DZ||_infinity=O(sqrt(epsilon/ell)). Core contributions satisfy these estimates as well; for example its weighted-gradient contribution is O(a^6)=o(A^2). Here A=O(epsilon/ell), uniformly in nearby R.

The vertical first-variation cancellation is exact to the needed order. On the upper reference cap s0=sqrt(R^2-r^2), the vector Ds0/sqrt(1+|Ds0|^2) equals -x/R. For compactly supported vertical change v,

    int (Ds0/sqrt(1+|Ds0|^2)) dot Dv = (2/R)int v.

The integral of v is exactly its signed volume change. The reflected lower cap has the same outward sign convention. The free equatorial correction restores exactly the lost inner volume, and the sphere's constant mean curvature gives area change (2/R) times that restored volume plus O(A^2). Thus the linear cap contributions cancel; they cannot leave an O(epsilon/ell) term. Correction supports are disjoint from polar supports.

The cap area Hessian at Ds0 is I+O(r^2), uniformly on the fixed chart. Its integrated quadratic error is bounded by C int r^2|Dv|^2=O(A^2), rather than a fixed O(d^2) relative error. The Taylor remainder is bounded by C||Dv||_infinity int|Dv|^2; divided by epsilon^2/ell^2 this is O(sqrt(epsilon ell))->0. The exact volume-correcting bump has area-minus-(2/R)volume O(A^2). Flat face linear area variations vanish, their quartic-gradient errors are smaller, and their own volume correction costs O(A^2). All corrections preserve inclusion on fixed positive-clearance patches and attain exact target volumes by an invertible volume equation.

Each of four patches has height magnitude Z/2 and half-Dirichlet area coefficient. Their sum is J/2+O(epsilon^2/ell^2). The profile is C1,1 with no vertical rims, sufficient for finite perimeter; no extra smoothing theorem is needed. Therefore

    M_B <= pi epsilon^2(H+1/4)/(H+1/2)^2+C epsilon^2/ell^2.

The defining equation implies 2H=ell+log(H+1/2)+log(d^2/R), hence H=(ell+log ell)/2+O_d(1). The last upper bound matches the lower bound. The recovery tends to the radius-R ball and lies in the fixed ball neighborhood eventually.

## Expansion, provenance, and verdict boundary

Expanding the reciprocal gives M_B=2pi S-2pi T2+o(T2), because epsilon^2/ell^2=o(T2). Direct differentiation gives g'(1/3)=-2pi/3 and bounded g'' nearby. Under the crossover hypothesis delta=3S+alpha T2+o(T2), delta^2/T2=O(epsilon^2/log ell)->0. The exact minimum identity then proves the asserted minimum of two limits. Formal log–log inversion and this algebraic corollary alone are not a contribution claim.

The review used the full candidate, its provenance/literature/reading records, R018, complete I275, complete I277 reconstruction/review, complete I346 proposal and analysis, and the actual retained scalar theorem and AFM pages. AFM's primary PDF was freshly opened at Definition 2.5 and Theorem 4.2. Only these exact external regularity contracts are used; their underlying classical regularity proofs are not rederived. The author support script and JSON were read, but the script was not executed because it writes into the author's directory. No numerical evidence is part of the verdict. Input hashes and exact reading extents are in provenance.json, including verification of the scalar TeX against the complete pinned tree. Local antecedents were independently checked above rather than accepted from verdict labels.

No substantive gap or required change remains under the stipulated scalar theorem and established AFM regularity input. The trace argument above expands the candidate's mollification sentence; it supplies the stated estimate without adding a hypothesis. This is PASS for full unrestricted and jointly uniform scope, not merely an upper bound or a radial/graph-restricted theorem. Independent contribution assessment remains separate.
