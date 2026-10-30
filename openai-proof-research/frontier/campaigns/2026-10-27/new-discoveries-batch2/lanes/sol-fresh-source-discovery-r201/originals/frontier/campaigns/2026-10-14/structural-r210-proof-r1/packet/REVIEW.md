# Structural210 independent proof review — round 1

**Full-scope correctness verdict: PASS, relative to the stipulated Source334 truth and the explicitly read classical smooth local-existence interfaces.** This verdict applies to the entire unchanged frozen statement and submitted proof. No essential mathematical change, removed clause, narrower replacement theorem, finite-regularity upgrade, or additional genericity assumption is needed. This is a correctness review only; no contribution verdict is assigned.

The reviewed statement has SHA256 `cd65e255f9fdb798bb38fd5e3291f2f657e7dae91c0af62fdf366e05ec075295`; the reviewed proof has SHA256 `f50ea4216bce7ad43d5a713dcc7fc180ad283ff22cb9dae14a0f1d26e4a24b24`. Both are the immutable submitted packet versions. The author's checks and assertion of no gap were read as claims to test, not as mathematical evidence. There were no prior review findings or author responses. All resolutions below are this reviewer's deductions from the submission and admitted dependencies.

The theorem classifies the sets B(g) in the open coordinate square D=(-1,1)^2 exactly as the relatively closed nowhere-dense sets. The forward construction also establishes all four additional requirements: uniform quadratic-form bounds, every curvature jet zero on C, only regular curvature zeros in D\C, and the full Euclidean metric jet at 0 when 0 belongs to C. The converse applies to every smooth positive metric without uniform coefficient assumptions. Empty C is included. No assertion about arbitrary finite-order immersions is included in this verdict.

## 1. Exact paid interface and its application

I authenticated all 12 Source334 blobs against the complete pinned preprint tree and read the main file, every operative section, all four figure sources, README and bibliography. The dependency is the actual fixed-exterior Proposition `prop:patch`, with its entire cap/pulse proof stipulated true, rather than just the source's headline nonimmersible germ.

The source uses S=[-3,3]^2, the tensor support P=[-1/10,1/10]^2, and the larger negative box [-1/5,1/5]^2. Its background is any fixed smooth positive metric near S with scalar curvature kappa(x^2-h(y)), kappa>0. The source h is even, equals 1 on [-1/2,1/2], is nonincreasing on the positive half-axis, is positive inside (-1,1), negative for |y|>1, and has a simple zero at 1. Thus the background lies in the source's open metric slice: on the larger box its curvature is at most -(24/25)kappa<-kappa/2.

An excluded height is smooth on a neighborhood of the closed square and satisfies, throughout S,

    det H = K det(g)(1-|dz|_g^2),
    E=det(g)(1-|dz|_g^2)>0,
    H_yy != 0,    |H_xy/H_yy| <= 1/100.

These match the submission. Positive definiteness converts its `1-|dz|_g^2>0` to the source's E>0. The perturbations are smooth symmetric tensors supported in P, keep the metric positive and K<-kappa/2 on the larger box, and preserve the whole exterior metric. Residuality in that slice supplies a point in every basic smooth neighborhood of the background. A basic neighborhood constrains finitely many seminorms, so the arbitrarily small finite-seminorm choices in §6 follow. This does not assert uniform estimates as kappa or a dilation tends to zero.

The operative reading confirms what is paid: the cap estimate starts with bounded C^8 smooth heights and positive lower bounds for g, |H_yy| and E. The flow domain and its margins come from |q|<=1/100. The differentiated transverse coefficient is (l+1)A_s+O_l(A), using the curvature-drift identity. The directed multiplier has a vanishing artificial-edge weight and is paired with a weighted elliptic estimate on the positive side; it requires no high-order boundary values on that edge. The upper and lower caps supply all-order endpoint data. Hyperbolic energy propagation reaches both pulse edges, and the fixed-background time-Taylor comparison isolates the forcing. Changing only g_theta,theta has principal curvature-density variation -1/2 partial_xi^2(delta g_theta,theta). The forcing moment is linear in the strip parameter delta, while competing spatial terms are quadratic. The source fixes class/neighborhood/background/slab/N first, delta second and frequency last. Its Baire argument excludes all smooth admissible heights. None of these stipulated operations is re-audited or replaced by a claim of finite-regularity smoothing.

For Phi(u)=c+lambda R u, one has

    Phi^*g = lambda^2 R^T(g composed with Phi)R,
    K_(Phi^*g) = K_g composed with Phi,
    Hess_(Phi^*g)(z composed with Phi) = lambda^2 R^T H R.

The gradient norm is intrinsic and unchanged. Both sides of the Darboux determinant equation gain lambda^4; the Hessian ratio is unchanged. Treating curvature as lambda^{-2} times the prescribed physical scalar here would be an error: this is the pullback of the whole metric, not an independent constant rescaling after pullback. The submitted proof uses the correct law.

## 2. Actual immersion, normal estimates, and norm conventions

In §2 the bars around the vector partial^alpha F mean Euclidean vector length, as specified in §1; M bounds each second and third coordinate derivative vector. The component definition of a C^m norm elsewhere does not change this meaning. For a hypothetical smooth F one can always enlarge a component bound by the fixed dimension factor to obtain this vector bound. No parameter in the construction depends on which hypothetical F is later considered.

Let A=F_X cross F_Y. The metric bounds give |F_i|<=sqrt(2) and |A|=sqrt(det g)>=1/2. Differentiating n=A/|A| gives the orthogonal projection of A_k divided by |A|, so

    |n_k| <= (|F_Xk||F_Y|+|F_X||F_Yk|)/|A|
           <= 4 sqrt(2) M < 6M.

Combining the two coordinate derivatives yields an operator bound at most 8M, hence the proof's 9M Lipschitz bound is conservative. Straight segments remain inside the convex ball. With e=n(c) and |x-c|<=4r,

    |n(x)-e| <= 36Mr <= .036,
    nu=<n,e> = 1-|n-e|^2/2 > 0.

Moreover the tangential projection of e has norm |dz|_g, which is at most |e-n|<1/2. These inequalities hold across the whole ball, not merely near a boundary point. The ambient vector e is fixed before choosing the boundary point and is never rotated as a scalar solution independently of F.

The Gauss formula gives H_ij=nu< F_ij,n >. Thus |II_ij|<=M and

    |partial_k H_ij|
       <= |nu_k||II_ij| + |nu|(|F_ijk|+|F_ij||n_k|)
       <= M+12M^2 <=13M^2.

A component changes by at most 13sqrt(2)M^2|x-y| along a segment; a 2x2 matrix has operator norm at most twice its largest entry. Therefore 26sqrt(2)M^2<100M^2 proves (2.1), including all component-to-operator factors. Uniform derivatives of the constructed metric are unnecessary here. The Gauss identities and the actual coordinate bounds on F supply the estimates.

## 3. Cofactor sign, flux, and rank-one lower bound

Put T^{ij}=(Delta_g z)g^{ij}-H^{ij}, with both indices of H raised. Covariant commutation gives

    nabla_i H^{ij}=nabla^j Delta_g z + Ric^j_k z^k,
    nabla_i T^{ij}=-K z^j.

In dimension two, T^{ij}H_ij=(tr(g^{-1}H))^2-tr((g^{-1}H)^2)=2 det(g^{-1}H). The actual height equation therefore yields

    div_g(T dz) = K(2-3|dz|_g^2).

This is the sign in Khuri2009 (6)-(8), independently recovered covariantly here. As a sign check, on the unit sphere a coordinate height has H=-zg and T=-zg^{-1}; its flux divergence is 2z^2-|dz|^2=2-3|dz|^2. The proof differentiates smooth functions, so there is no weak-solution or integration-by-parts regularity issue.

On the disk, K<0 and 2-3|dz|_g^2>=5/4>1. Its radius-r/2 core has K=-a and volume density at least 1/2, giving an absolute interior integral at least pi a r^2/8. The outward conormal in (2.3) is a covector of g^{-1}-norm one. Consequently |mu|<=sqrt(2), while |dz|<=sqrt(2)/2, and their Euclidean product is at most one.

Writing H*=max_boundary ||H||_op, one has |tr(g^{-1}H)|<=4H*, whence

    ||T||_op <= 2(4H*)+4H*=12H*.

The g-length of the circle is <=2pi sqrt(2)r<9r. Hence

    pi a r^2/8 <=108r H*,
    H* >= pi a r/864 > a r/1000 = h0.

All factors of a,r,M are in the right places: the flux supplies ar, and M enters only in the continuity radius sigma=h0/(10^6 M^2). Compactness of the circle gives a maximizing point b. At b, K=0 and the height equation gives det H=0; H is nonzero by the lower bound. A real symmetric 2x2 nonzero matrix of determinant zero has rank one. No graph representation or boundary value condition for z is required.

## 4. Finite geometry and uniform capture

The angular net is a finite net of unoriented lines in the fixed Euclidean parameter plane. This is the appropriate plane for the affine rotations, even though g need not be Euclidean there. A sigma/10-net on the compact circle is finite. For every boundary-net point and angle, an exterior open collar contains infinitely many possible centers within sigma/3, so finitely many distinct centers can be chosen. Afterward, the minimum of their finitely many positive mutual separations and distances to the disk/collar boundaries is positive. Shrinking each positive scale gives disjoint closures of the full images of [-4,4]^2. The same shrinking places every such image within sigma/2 of its designated boundary-net point. This is independent of any immersion and of the later b and kappa choices.

For the rank-one form at b, write H=signed_s vv^T with |signed_s|=s>=h0. The selected rotation has error |theta|<=.001 from its kernel, so |H_yy(b)|=s cos^2(theta) and |H_xy(b)|=s|sin(theta)cos(theta)|. Every point of the selected full patch has distance at most .6sigma from b; using the proof's looser bound sigma gives matrix error delta<=h0/10000. With t=delta/s<=10^-4,

    |H_xy(x)/H_yy(x)|
      <= (|sin(theta)cos(theta)|+t)/(cos^2(theta)-t)
      <= .0011/.999899 < .001101 < .01.

The denominator is positive, proving the nonvanishing assertion on the whole patch. The already established |dz|_g<=1/2 applies there as well. The affine pullback then supplies all source inequalities on S, and smoothness on a neighborhood of S follows from F's domain containing the closed block. There is no assumption of a common kernel or common normal across different hypothetical immersions.

The finite block only excludes smooth immersions of the whole block with its assigned derivative bound. It need not contain a point lacking a local immersion; indeed the final proof shows all points of each block have local immersions. These statements are compatible because neither the local maps nor their neighborhoods or derivative bounds are uniform.

## 5. Two amplitudes, cutoff derivatives, and absence of circularity

The construction fixes r,M,m,epsilon and beta first, along with the finite C^m multiplication norm T for beta. For fixed radial cutoffs, derivatives of rho=|x-c| on each interpolation annulus satisfy |D^j rho|<=C_j r^{1-j}. Near c the profile is constant, so no singular radial derivatives occur. Since b<=a/r, b(rho-r) and its cutoff interpolations obey |D^j k_(a,b)|<=C_j a max(1,r^{-j}), uniformly in b. Negative/negative and positive/positive convex interpolations have the stated strict signs. The linear collar contains all eventual full patches and crosses zero only at rho=r, with derivative b>0.

Choose a<=1 so that the complete radial profile pays T C'_m(r)a<epsilon/4. Then and only then choose sigma, the finite nets, centers and scales. This order may make the finite set extremely large and the scales extremely small; neither is prohibited. It leaves a fixed throughout the remaining choices.

For an ordinary cutoff chi with values in [0,1], equal to one near S and supported in (-4,4)^2, the patch correction is chi_phys[kappa q composed with Phi^{-1}-b(rho-r)]. Its derivatives of order <=m are finite sums of products of fixed cutoff derivatives, powers of lambda^{-1}, derivatives of q=x^2-h(y), and derivatives of rho on a fixed annulus. For example, model terms have bounds C_(p,j) kappa lambda^{-j}, and old-profile terms are b times finite constants involving lambda^{-ell}r^{1-j+ell}. Thus (4.3) is valid for the already fixed geometry. There are finitely many p,j, so a strictly positive b can satisfy all b-cost inequalities and b<=a/r; then strictly positive kappas can satisfy all remaining costs. The minimum of finitely many positive permitted bounds remains positive. No new restriction on a is imposed.

The standard cutoff convention 0<=chi<=1 is implicit in the word cutoff and the convex combination (4.2); beta's range is explicitly stated. Taking these usual cutoffs is already a permitted choice in the submitted construction, not a change to it. Their derivative bounds are finite because the geometry has been fixed. Multiplication by beta contributes T times the correction budget; combining <epsilon/4 for the old profile with <epsilon/(4T) for all corrections gives <epsilon/2 as claimed.

Every transition for chi lies outside S. There q>0: if |x|>=3, then x^2-h(y)>=8 because h<=1; if |y|>=3, then h(y)<0. The old collar curvature is strictly positive because the patches avoid the closed disk. Their convex combination is therefore strictly positive, including cutoff endpoints. Within the model, dq=(2x,-h'(y)). At a zero with x!=0 the first component is nonzero; with x=0, y=+/-1 and the second is nonzero. Invertible affine pullback and positive kappa preserve regularity. The disk's circle remains untouched and has b>0. All zeros of each finite profile are therefore identified and regular.

## 6. Arbitrary relatively closed nowhere-dense sets

Let C be nonempty and E=D\C. A countable basis of relatively compact coordinate balls can be filtered to those meeting C and scheduled with every member repeated infinitely often. The procedure is existential; no effective membership decision is claimed. At each stage a point p_n of C in the scheduled ball has positive distance from the finitely many earlier compact blocks. A sufficiently small ball around p_n remains in the scheduled ball and D and misses the previous blocks. Since C has empty relative interior, this ball contains a point of E as close to p_n as desired, hence with dist(c_n,C)<2^-n. Openness of E gives a positive allowable radius around c_n. Imposing 4r_n<dist(c_n,C)/2 and the stated radius bounds then constructs the next disjoint closed block.

For each p in C and each neighborhood of p, select a basis ball containing p and lying in that neighborhood. Infinitely many scheduled stages place centers in it. Selecting progressively smaller neighborhoods and later stages constructs a subsequence c_(n_k)->p with n_k strictly increasing. Thus the needed indices tend to infinity even for isolated points of C; this is stronger than merely obtaining p in the closure of an unspecified finite-index set.

For x in B_n,

    dist(x,C) <= dist(c_n,C)+4r_n < (3/2)2^-n.

A compact Q contained in E has positive distance from C. One way to see this despite relative rather than global closedness is to suppose distance zero, extract q_j->q in Q, and obtain nearby c_j in C converging to the interior point q; relative closedness would put q in C, a contradiction. Therefore only finitely many blocks meet Q. This proves local finiteness throughout E. No compactness of C, measure-zero property, countability of C, or density of the centers in D is used. Accumulation toward the boundary of D does not harm a local assertion in D.

## 7. Positive background and curvature series

E is open and second countable, so a countable family of nonnegative smooth compactly supported bumps in E can have positivity sets covering E: choose relatively compact basis balls and bumps positive on smaller balls that still cover. Each support is a compact subset of E, so by §6 it meets only finitely many blocks. A coefficient t_j therefore faces finitely many constraints: orders <=j globally and, for each of finitely many intersecting B_n, orders <=n. All norms are finite and all prescribed right sides positive, so t_j>0 can be chosen to meet them simultaneously.

For each fixed derivative order ell, terms j>=ell have a uniformly summable derivative bound 2^(-j-20). The finitely many earlier terms are smooth with bounded derivatives. Extending each bump by zero to R^2 gives a globally smooth function, and the uniformly convergent derivative series yields a smooth sum on R^2. Every individual bump vanishes on a neighborhood of each point of C; evaluating the derivative series shows every derivative of k_+ is zero there. Positivity on E follows because at every point at least one term is positive and all coefficients are strictly positive. There is no need for a uniform lower bound for k_+ near C.

For a fixed block, summing the second constraints over j gives ||k_+||_(C^n(B_n))<=gamma_n because sum_(j>=1)2^-j=1. Hence

    ||beta_n(k_n-k_+)||_(C^n)
      <= ||beta_n k_n||_(C^n)+T_n gamma_n <epsilon_n.

These terms extend smoothly by zero and individually vanish near C. Their tails n>=ell are uniformly summable in every fixed derivative order ell. This gives smooth K0 with all jets zero on C and ||K0||_infinity<2^-19<10^-3. The proof uses derivative bounds, not merely support disjointness or amplitudes tending to zero.

On the radius-2r_n ball, K0=k_n. In the beta transition, k_n=a_n>0 and k_+>0, so K0 is a positive convex combination. Off the blocks, K0=k_+>0 in E. Local finiteness in E excludes any unnoticed accumulation zero there. Thus the only zeros in E are the disk circles and the affine model curves, all regular. Positive-measure C causes no problem: the uniform derivative-series argument holds pointwise on all C, without a measure assumption.

## 8. Curvature ODE, uniform bounds, and the conditional jet

For every fixed Y, the linear ODE f_XX=-K0 f with f(0,Y)=1 and f_X(0,Y)=0 has a solution on the whole horizontal interval (-1,1). On compact subintervals this is standard linear ODE continuation; the bounded curvature and the following estimate prevent finite-distance blowup. Smooth parameter dependence on compact rectangles yields f smooth on D, even if high derivatives of K0 are not uniformly bounded up to the boundary of D.

The Volterra equation, for positive or negative X, bounds the integral kernel by |X|^2/2<=1. On each segment joining 0 and X,

    sup|f-1| <=10^-3 sup|f|,
    sup|f| <=1/(1-10^-3),    |f-1|<.002.

For gbar=diag(1,f^2), the potentially nonzero Christoffel coefficients are Gamma^X_YY=-f f_X, Gamma^Y_XY=f_X/f, and Gamma^Y_YY=f_Y/f. The curvature computation cancels the Y-derivative terms and gives K_gbar=-f_XX/f=K0 exactly. This is not an approximate prescription or a locally supported change to a background metric.

The initial line is essential. At a general p in C, f(p) and f_X(p) can depend on curvature at other points of its horizontal segment; flat curvature at p alone does not imply gbar-I flat there. The frozen statement requires that metric jet only at 0 if 0 in C. At that point the initial conditions give all mixed derivatives with X-order 0 or 1. For X-order a>=2,

    partial_X^a partial_Y^b(f-1)(0)
      = -partial_X^(a-2)partial_Y^b(K0 f)(0)=0,

since every product term contains a derivative of K0 at 0. No induction in unknown jets beyond this identity is missing. Squaring f preserves the Euclidean metric jet.

## 9. Final tensor perturbations and the actual final curvature

There are countably many patches, finitely many in each block. At each patch the pullback background is positive near S and has exactly the required scalar curvature; all scales and kappas have already been fixed. For an individual perturbation eta,

    eta_hat(X)=lambda^-2 R eta(Phi^-1(X)) R^T,
    ||D^m eta_hat|| <=C_m lambda^(-m-2)||D^m eta||.

For a complete C^m norm, apply this estimate separately at every order k<=m, or take the maximum of the finitely many scaling constants. Thus finitely many source seminorm constraints suffice for every requirement m<=p in (6.1). There is no assumption that the source controls infinitely many seminorms at once, nor that its constants are uniform across patches. Extension by zero is smooth because the tensor is supported in the central box strictly inside the full patch.

For each fixed m, the tail p>=m is uniformly summable in C^m, and the earlier finite sum is smooth. Each term vanishes near each point of C, so the sum has all derivatives zero on C. With the submitted component convention, the zeroth-order component sum is at most sum_(p>=1)2^(-p-10)=2^-10, and its operator norm is at most 2^-9<1/8. Thus even without spending the full stated 1/8 allowance,

    g >= ((.998)^2-1/8)I > (1/2)I,
    g <= ((1.002)^2+1/8)I <2I.

Each full patch sees exactly its own tensor perturbation. A closed negative disk has a neighborhood avoiding all tensors: the disk is compact in E, so only finitely many blocks can approach it locally, and their closed supports are disjoint; its own block has only finitely many separated central boxes. This makes the prescribed negative disk, half-radius mass and zero boundary exact for the final metric. The argument does not rely on compact disjoint sets being uniformly separated from an arbitrary infinite family without local finiteness.

Curvature can change only in the affine images of P. On each such image the source gives strict negativity on the larger affine image of [-1/5,1/5]^2. The prescribed curvature was already strictly negative there. Outside the central boxes the metric equals gbar; at their boundaries smooth compact support makes the same jets agree as well. Hence no zero is created, removed, or made degenerate there, and

    K_g^{-1}(0)=K0^{-1}(0)

on all D. At any zero in E, local finiteness and the finite geometry give a neighborhood avoiding all tensor supports, so K_g=K0 nearby and dK_g!=0. At C, every metric jet of g equals that of gbar. Curvature derivatives are finite-jet smooth expressions in a positive metric, and therefore all derivatives of K_g at C equal those of K0 and vanish. The tensor sum is also flat at 0 when 0 in C, completing the conditional metric-jet requirement for the final metric, not just gbar.

## 10. Capture of one arbitrary local smooth immersion

Fix p in C and suppose a C-infinity immersion F exists on an open neighborhood U. Take a closed coordinate ball about p strictly inside U. All second and third coordinate derivative vectors of F are bounded there by some finite M. The block subsequence approaching p has indices tending to infinity, r_n->0 and assigned bounds M_n=n+1. A sufficiently late block is entirely inside the chosen ball and has M_n>=M.

The final metric meets every hypothesis of §§2-3 on this block, including its exact negative disk and curvature mass. Use the one fixed ambient normal at that block center. The flux and modulus estimates select one of the already constructed spatial/orientation patches and force the actual smooth height to be admissible on its full model square. Pullback of the final metric there is precisely the source-obstructed metric. This contradicts the paid patch proposition.

All choices of metric, blocks, scales, curvature profiles, and source perturbations precede this hypothetical F. Only the index and the selected patch depend on F. This proves C subset B(g) point by point. It neither takes a limit of obstructed metrics nor a compactness limit of immersions. It does not claim any individual block obstructs all smooth immersions, and it does not turn a bound on derivatives of a smooth candidate into a nonsolvability theorem for arbitrary C^3 candidates. Smoothness remains required by the source height obstruction.

## 11. Actual primary existence and the reverse inclusion

I visually read the actual Nakamura–Maeda KSTS/RR-86/011 report, dated October 22, 1986, at the extents recorded in READ-LIMITS.md. Its Theorem A (printed p.2; PDF p.3) states smooth local isometric embedding near a point of a smooth Riemannian surface with K!=0. Its Theorem C (printed pp.2-3; PDF pp.3-4) states local C-infinity isometric embedding near K=0,dK!=0. These are actual statements in the original report, not inferred from a citation or from finite-differentiability theorems with shrinking domains.

The operative proof reading included the linearized embedding system, the real-principal-type definition, and the two-dimensional principal-symbol calculation. In clean-zero coordinates the displayed polynomial is -(xi_1^2+x^1 xi_2^2); at the degenerate characteristic x^1=xi_1=0, xi_2!=0 its base derivative in x^1 is nonzero, while the canonical one-form has the transverse xi_2 dx^2 direction. The report then constructs approximate principal-type embeddings and applies its nonlinear solvability theorem. The iteration's low-order convergence is followed by bounds and interpolation proving convergence of the same sequence in arbitrarily high Sobolev orders (printed pp.18-20, including (3.41)-(3.53)). This produces one smooth map on one neighborhood. The tame right-inverse construction, correction of the small remainder, and appendix interfaces A.5-A.6 were read; the section-4 application was read. It is an existence procedure for a new map, not a regularity theorem for every finite-regularity solution.

The preprint has evident numbering/theorem-letter inconsistencies, including calling the clean-zero calculation “Theorem B” in one lemma despite its displayed dK hypothesis. The actual Theorems A/C and the displayed two-dimensional calculation determine the interface used here. I do not identify the 1986 text with the 1989 published version. The retained author access record reports HTTP 403 at the latter endpoint; that failure was not independently repeated in this review. The unread report pages and untraced Fourier-integral references are explicitly disclosed. The scope required here is the stated classical smooth existence interface and its operative construction, not a new proof of the entire foundational microlocal theory.

For every q in E, either K_g(q)!=0 or K_g(q)=0 and dK_g(q)!=0 by §9. The first case satisfies Theorem A; the second satisfies Theorem C. By continuity and smoothness all are local hypotheses at q and require no global sign restriction, uniform curvature lower bound, or common neighborhood across q. Each application gives a smooth local embedding, hence a smooth local immersion after any needed restriction inside D. This covers disk circles, model zero curves, all transition points and all remaining points of E. Therefore B(g) subset C. This essential reverse inclusion has not been left conditional on an unidentified local-existence lemma.

The other primary readings prevent stronger substitutions. NY2002 v1 claims smooth sign-restricted metrics with C^3/C^(3,alpha) nonembedding and uses negative disks, orientation arrangements, flat concave extensions and an embedding-norm perturbation construction. NY2008's actual published theorem instead has a C^(2,1) metric and no local C^2 embedding; its p.320 leaves the arbitrary smooth problem open. That version discrepancy remains unresolved and supplies no premise here. Khuri2007's coefficients depend on u and its first jet; its Legendre reduction and adjoint moment construction do not automatically produce coefficients of a metric Darboux equation. Khuri2009 actually provides the cofactor calculation, prescribed-curvature ODE and solution-dependent reduction; its proposed nonsolvable curvature profile is explicitly left open. The submitted proof uses none of these papers as an unproved replacement for Source334.

## 12. Empty set, converse, and complete quantifier check

For C empty, choose for example epsilon=10^-2 in the submitted metric diag(1,cos^2(sqrt(epsilon)X)). It has scalar curvature epsilon>0 and lies between (1/2)I and 2I throughout D. Theorem A applies at every point. The curvature-flatness and conditional metric-jet clauses have no points to test, and there are no curvature zeros, so item 4 is also satisfied. No special patch construction is needed.

For any smooth positive metric, the union of neighborhoods carrying a smooth isometric immersion is open. Its complement B(g) is relatively closed. The nonzero-curvature theorem gives B(g) subset {K_g=0}. If B(g) contained a nonempty open V, K would vanish identically there. On a small contractible coordinate neighborhood in V choose a smooth oriented orthonormal coframe (theta^1,theta^2). Its connection form omega has d omega=0 because K=0. The Poincare lemma gives a potential; rotating the coframe by its angle, with the sign determined by the structure equations, gives two closed independent one-forms. Their local primitives u,v have nonsingular differential and g=du^2+dv^2. Thus (u,v,0) is a smooth local isometric immersion, contradicting membership in B(g). No global simply connectedness or global flat coordinates are asserted. Relative closedness plus empty interior is exactly relative nowhere density.

Every frozen quantifier is accounted for: for each relatively closed nowhere-dense C there is one globally smooth positive g on D; its coefficient bounds hold everywhere; B(g)=C uses arbitrary open neighborhoods and arbitrary smooth candidate maps; all curvature partial derivatives vanish at every point of C; all complementary curvature zeros are regular; the metric jet is Euclidean only at the stipulated origin when it belongs to C; and the converse has no coefficient-bound premise. The prefreeze finite-regularity route remains unproved and unused. There is no implicit stability, ambient genericity, prescribed metric jet at all C, whole-domain immersion, or embedding on a fixed common domain.

## Objections examined, resolutions, and remaining obligations

The substantial potential failures were the sign of the cofactor term, vector/component constants, choosing the height in a fixed ambient direction, source dilation laws, tiny-patch derivative costs feeding back into disk mass, accumulation on noncompact or positive-measure C, unintended final curvature zeros, and mistaking finite-order existence for smooth existence. Sections 1-12 above resolve them from the submitted choices and actual read interfaces. These are explanations of valid steps of the unchanged proof, not repairs to a defective construction. The ordinary cutoff range and the vector interpretation of |partial^alpha F| are consistent with the declared conventions.

No essential mathematical obligation remains for the frozen scope relative to the stated dependencies. The external dependencies remain explicit: the stipulated Source334 patch proposition including its full operative proof, and the classical smooth local existence Theorems A/C as read in the 1986 report. The report is not claimed to have been completely read or identified with the inaccessible 1989 text. The published/preprint NY discrepancy remains a bibliographic limit, not a gap in the present deduction. No unsupported finite-regularity theorem is used to discharge it.

The pinned Lean comparator was authenticated and read. Its endpoint `exists_local_metric_without_local_immersion` ends in `sorry`; the coordinate-square openness lemma supplies no endpoint proof. No compilation or formal verification of this result is claimed.

Artifact authentication and exact-selection/mode verification establish only the identity and preservation of reviewed files. They are separate from this mathematical correctness verdict. All protected source, primary, history and render bodies and their named metadata stay private/local in this review root under their original rights. The review never consulted the contribution peer, parent work, excluded rounds, or their results/status.
