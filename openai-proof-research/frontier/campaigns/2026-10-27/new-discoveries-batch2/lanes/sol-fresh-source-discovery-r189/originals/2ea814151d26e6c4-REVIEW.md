# Structural220 — independent round-one correctness review

Reviewer provenance: Codex / GPT-6 Astra / xhigh / default. Date: 2026-10-24. This is the correctness role only. No prior review, author response, peer result, or parent mathematical verdict was used. Parent alone adopts grades; this report assigns no contribution, acceptance, or campaign count.

**Role verdict: PASS for the entire unchanged frozen STATEMENT.md and submitted PROOF.md, under the stipulated truth of the pinned upstream results.** No essential mathematical repair, hypothesis change, exponent change, branch-dependent gauge, or replacement proof is needed. There are no unresolved essential correctness obligations. The detailed derivations below expand and challenge the submitted steps; they do not replace the nominee with a narrower theorem.

This verdict includes the auxiliary density estimate, nonvacuity argument, and the continuity/compactness baseline at its expressly stated smooth positive-limit scope. It is not a judgment about contribution, priority, formal coverage, or geometric realization.

One scope clarification deserves attention: the middle residue is unprescribed in the list of assumptions, but the exact cut-pair condition and exterior normalization actually force **B=I**, even for positive defect. The submitted weaker estimate (25) is nevertheless valid. “Free in the hypotheses, not fixed equal to I” (STATEMENT 54) cannot be read as an existence claim for admissible charts with B≠I. The statement contains no such existence assertion. This is a consequence of the unchanged assumptions, not an additional condition imposed to obtain the verdict.

## 1. Identified submission and scope

All locations below use one-based LF-byte lines: split the original bytes at byte 0x0a, retaining form feeds inside lines. Byte intervals are half-open. This is also the parser used for primary boundary classification and extraction.

- STATEMENT.md: all 3,180 bytes, lines 1–55; SHA256 `4c71274685f1401193eccbc7c6997b56d1ca2db88fef14cba159d638260aa35d`.
- PROOF.md: all 21,137 bytes, lines 1–308; SHA256 `efd13b45cbf17c3620c6bedc00152b1deb42e7cd6f7d37898019ded5aa6b5775`.
- DERIVATIONS.md: all 9,118 bytes, lines 1–46, including its non-nominated geometric baseline.
- COMPARISON.md: all 16,070 bytes, lines 1–63. Its coverage assertions were treated as author assertions, not my own reading.
- FINAL.md: all 2,878 bytes, lines 1–18, following a failed overlong range request that displayed no body.

The theorem fixes arbitrary m,k≥1, d=m+k, q≥2, K≥1, and 0<a<D/2, with D=π/2, T=π and r0=π/64. Its conclusion is simultaneous for every integer 0≤j<q, on both components of J_a, with the same specified symmetric constant R_D(D), and exponent 3(1−j/q)/(4(d+9)). The smallness threshold is exactly min(r0,a/4)^[4(d+9)/3]. Constants may depend on m,k,q,K,a only. These are the actual quantifiers reviewed.

The source's geometric dimensions do not limit the candidate's arbitrary positive m,k: the operative weighted and matrix identities are algebraic/analytic for every such pair. Conversely, no abstract chart is claimed to come from a Riemannian manifold. Source classification and global geometric machinery cannot be used as a substitute for this chart argument; the submission does not do so.

## 2. Hypotheses, atlas and middle residue

Locations: STATEMENT 5–35, 47–54; PROOF 9–17, 199–205, 232–249, 296–305.

A'>0 makes its principal block H' positive and its velocity Schur complement S positive on I. The prescribed C^q extension through D and H'(D)>0 make H'>0 throughout (0,T). Consequently H(y)−H(x)=∫_x^y H' has the sign of y−x and is invertible for every distinct endpoint pair, including pairs crossing D. The derivative ranges needed for this argument are available already from q≥2; no hidden q+1 regularity is used.

The five atlas regions cover I: the three pole neighborhoods of radius 4r0 overlap the two interior intervals [r0,D−r0] and [D+r0,T−r0]. Off-diagonal pole residues vanish, so C' is uniformly bounded on the whole domain. Near D both H' and C' are bounded, and H' inverse is bounded by K sin²t I. On J_(a/2), rational pole derivatives through order q are uniformly bounded using the fixed pole distance and B≤KI. Thus the asserted interior C^q bounds are uniform in the individual chart.

There need not be any admissible chart for every small K, especially K=1 with the demanding Frobenius C^q atlas norm. This causes no quantifier failure: the theorem is conditional on the hypotheses, and its example claims existence for some sufficiently large finite K, not for each K≥1.

**Adversarial objection: can B actually vary independently?** No. As u↓0, the unchanged expansions imply

    V(u+D)−V(u) = (I_k−B)/u + O(1),
    C(u+D)−C(u) = O(1),
    H(u+D)−H(u) = I_m/u + O(1).

The last inverse is O(u). Hence Q(u,u+D)=(I_k−B)/u+O(1). Multiplication by u and the exact zero cut condition force B=I_k. This reasoning uses only admitted hypotheses; it does not audit a source theorem. A possible author response that “free” means “not assumed equal to I” resolves the formal-statement issue without changing content: that is exactly the qualification in STATEMENT 54. A response asserting actual admissible B≠I would be false. The proof's weaker O(rho^(3/2)) recovery remains a valid inequality, and its derivation below does not secretly assume B=I. No independent-residue nonvacuity claim receives this PASS.

## 3. Block algebra and every endpoint order

Locations: PROOF 19–54, equations (1)–(5); source 02-lagrangian.tex 392–542.

Set ΔH=H(y)−H(x), ΔC=C(y)−C(x), R=ΔC(ΔH)^−1. Block congruence by [[I,−R],[0,I]] and its transpose gives diag(Q,ΔH), hence det ΔA=det ΔH det Q. The same elimination for A' gives det A'=det H' det S. Absolute values in f therefore give the exact factorization (1), with no positivity assumption on ΔA or ΔH when y<x.

Differentiation in y gives

    Q_y=V'(y)−C'(y)R^T−R C'(y)^T+R H'(y)R^T
       =S(y)+(R−C'H'^−1)H'(R−C'H'^−1)^T.

Differentiation with −∂_x yields the same expression evaluated at x. All factors have their stated order; no matrices have been commuted. In particular negative ΔH does not reverse these derivative inequalities. The diagonal expansion Q(x,y)=(y−x)S(x)+o(|y−x|) is valid since H'(x) is invertible. Endpoint exchange gives Q(y,x)=−Q(x,y), including cut zeros.

For u<v, fixing x=u+iD and moving y from u+jD to v+jD gives Q_ij≥I_j. Fixing y=v+jD and integrating −Q_x from x=u+iD to v+iD gives Q_ij≥I_i. With i=j the diagonal endpoint is reached by a limit; with i≠j it is a cut zero. When (i,j)=(1,0), the whole path has x>y, neither moving endpoint meets a pole or the actual diagonal, and both inequalities still have the displayed direction. Thus all four Q_ij are positive definite. This directly resolves the most plausible endpoint-sign objection without modifying (2) or (3).

For P>0, writing P=pN, det N=1, turns D_P into log det E_mu N. Concavity of logdet proves D_P≥0. Q_ij≥I_i,I_j separately gives log det Q_ij≥max(log det I_i,log det I_j), so E_ij≥0. These are positive slacks, not absolute values masking sign errors.

## 4. Scalar cancellation, exact multiplicities and integrability

Locations: PROOF 56–109, equations (6)–(9); source 03-weighted-comparison.tex 25–124 and 145–334; Kazdan E.4–E.16.

The chord formula follows from integrating λ²csc²(λt). For a bounded g and the stated symmetric W, let

    K_W(z)=W(z)/sin(λz),  I_W=∫_0^b W,
    F(t)=∫_(x<t<y) K_W(y−x)sin(λx)sin(λy) dx dy.

The bounded kernel makes F absolutely continuous. Differentiating its moving integration limits, using reflection z↦b−z, gives F'=I_W sin(λt)cos(λt), hence F=I_W sin²(λt)/(2λ). Since ∫W/P_b=F/λ, the coefficient of g(t) is p_b(t)F(t)/λ=I_W/2. The endpoint coefficient is also I_W/2 by symmetry. This proves (6), without differentiating W or integrating p_b over its entire singular interval.

**Normalization objection and resolution.** The abbreviated sentence at PROOF 74 describes “the double integral after inserting the chord identity.” Its displayed derivative is that of F, not F/λ. The exact cited source explicitly separates the factor 1/λ (source 03, lines 68–100). Keeping it outside the double integral gives the claimed coefficient for both λ=1 and λ=2. Thus the quoted scalar identity and both applications are correct as submitted; no change of scalar weight or missing factor in (8) is needed. The distinction is made explicit here so that the shorthand cannot be misused.

For the full-period block the exact logarithm is D_H+m[A_H−(g_H(x)+g_H(y))/2]. For a folded K block it is E_ij+(D_i+D_j)/2+(k/2)[A_i+A_j−g_i(u)−g_j(v)]. The fast reference chord is sin(2(v−u))/2 for all four actual endpoint choices, including reversed order. The actual slow factors are sin^m z on the diagonal choices and cos^m z on the off-diagonal choices.

The row and column sums of w_ij are W_D. Therefore summing weighted (D_i+D_j)/2 gives W_D∑_i D_i, while summing the scalar bracket with k/2 gives kW_D∑_i[A_i−(g_i(u)+g_i(v))/2]. The four folded triangles and their transposes are eight disjoint regions covering the square apart from finitely many lines, all with Jacobian one. Endpoint exchange contributes exactly the outer factor 2. Consequently (8) has coefficients 2m, 2, 2k, 2, 2, 1 exactly as printed. H cancellation uses w(T−z)=w(z), w/sin z bounded; the two fast cancellations use W_D(D−z)=W_D(z), W_D/sin2z bounded. These include m=1 and k=1.

Every final term is nonnegative: scalar Jensen, matrix logdet Jensen, monotonicity slack E, and Φ. Scalar linear terms cancel only by the proved finite identity; no matrix error can be cancelled against another block.

Finiteness is also valid. If L_H,L_K denote the two logarithmic ratios, determinant-root bounds and K give L_H≥−2m log K and L_K≥−2k log K. For L=L_H+L_K, wL^+≤f. Hypothesis 5 makes f bounded, hence integrable, on the compact square. The separate lower bounds then bound each individual positive part by L^+ plus a constant. Thus wL_H, wL_K and wL are absolutely integrable before any subtraction. Bounded g gives absolute Fubini for the scalar terms. D_i,D_H,E are nonnegative and the exact finite identities force their weighted integrability. Pole, cut and diagonal lines have planar measure zero; assigning logarithms arbitrarily there introduces no infinite-minus-infinite operation.

For (9), Φ(r)−(sqrt(r)−1)²=2(sqrt(r)−1−log sqrt(r))≥0. Integrating and using (8) gives the square-root density bound. Cauchy–Schwarz and (sqrt f+sqrt w)²≤2(f+w), with ∫f=W+Delta, give exactly sqrt(Delta(4W+2Delta)). This estimate is auxiliary, not a substitute for chart control.

## 5. Uniform variance estimates and endpoint concentration

Locations: PROOF 113–160, equations (10)–(16).

For |g|≤L, the exponentially tilted probability density is at least exp(−2L) relative to the reference measure for every tilt parameter in [0,1]. The variational formula Var(g)=inf_c E(g−c)² proves the same lower comparison for variance. Integrating F''(s) against 1−s gives (10) with exp(−2L)/2. This is valid for arbitrary probability measures and bounded profiles, not merely smooth samples.

For symmetric U and 0<Z≤ΛI, diagonalizing Z shows

    tr(Z^−1 U Z^−1 U)=∑_(a,b) U_ab²/(z_a z_b)≥Λ^−2||U||_F².

This does not require U to commute with Z. The region 0<Z≤ΛI is convex, contains N and its mean, and here Λ=K². Taylor's integral formula cancels the averaged linear term and proves (11). The lower spectral bound K^−2 also ensures all logdet expressions are well defined. Applying this to M_H and M_i is legitimate; their determinant is one and their spectra lie in [K^−2,K²].

The rectangle area is (rho/4)²=rho²/16. Its intervals enclose [rho,b−rho]. The chord integral is λcot(λx)+λcot(λ(b−y))≤1/x+1/(b−y)≤8/rho, while p_b≥λ². Thus the reference density on the common interval is at least λ²rho/8. Actual h- or s-weighted probabilities dominate the corresponding reference probability by K^−2, because both the profile and its integral have the stipulated ratio bounds.

Using the pairwise variance identity and restricting both variables to the common interval costs rho². Its length is at least b/2, so the identity ∫_K∫_K||F(t)−F(s)||²=2|K|∫_K||F−mean_K F||² leaves a uniform constant. Subtracting I in the matrix profiles has no effect on variance.

In the T rectangle, T−(y−x)∈[rho/2,rho]; the sine inequalities give both slow and fast factors ≥rho/π and hence w≥(rho/π)^d. In the D rectangle, sin(y−x)≥1/sqrt2 and the fast factor ≥rho/π, giving both w_ii and W_D at least 2^(−m/2)(rho/π)^k. All trigonometric arguments lie in the stated range because rho≤r0. Multiplying the density, area and weight factors gives exactly d+4 and k+4 in (15)–(16).

An error concentrated near an endpoint does not defeat these estimates: no pointwise division by a vanishing weight occurs. The enclosing endpoint rectangles have positive area for every rho>0, and their common-domain lower density controls the unweighted interior variance. The subsequent exterior calibration handles the unknown mean.

## 6. Noncommutative coupling estimate

Locations: PROOF 164–195, equations (17)–(20); Boyd–Vandenberghe A.5.5.

Write G=∫H', U=∫C', and Lbar=UG^−1. Expanding ∫(L−Lbar)H'(L−Lbar)^T gives

    ∫L H'L^T − U G^−1 U^T,

because ∫LH'=U=Lbar G and G is symmetric. Combining V'=S+LH'L^T with the endpoint definition of Q proves (17) exactly in its written order. Noncommuting profiles cause no omitted term.

On a same-half rectangle, both endpoint V matrices are bounded by C/rho using their adjacent pole residues and bounded remainders; B≤KI suffices for this estimate. Because ΔH>0, the subtracted Schur term is positive semidefinite, so Q≤V(y)−V(x)≤(C/rho)I. Also P=∫S>0 and R=Q−P≥0.

Along P+tR≤Q, inverse order gives (P+tR)^−1≥Q^−1≥lambda_max(Q)^−1 I. Taking its product with R inside a trace is order preserving even without commutation. Thus logdet Q−logdet P≥lambda_max(Q)^−1 tr R. H'≥K^−1 I and (17) then give c rho∫||L−Lbar||². Restriction to the enclosed K and minimization over a constant matrix gives the unweighted variance lower bound. No equality between a weighted and unweighted mean is assumed.

Multiplication by rectangle area rho² and w_ii≥c rho^k gives k+3, exactly (20). A determinant-root estimate alone would not suffice; the submitted logdet-to-trace step supplies the missing information. This discharges the coupling objection at the full matrix scope.

## 7. Calibration, one scale and the rate

Locations: PROOF 197–269, equations (21)–(28).

Near an exterior pole, H'=t^−2 I+O(1), V'=t^−2 I+O(1), C'=O(1), and H'^−1=O(t²), all uniformly from the atlas and spectral bounds. It follows that P_H=I+O(t²), P_S=I+O(t²), L=O(t²), and the analogous right-end estimates hold. The normalized positive spectral region is compact, so determinant roots, division by those roots, and logarithms are uniformly Lipschitz there. This proves the stated O(t²) estimates for g and M−I. They are not constants depending on an unbounded individual chart.

For any variance bound C Delta rho^(−p), averaging over [rho,2rho], of length rho and contained in [rho,b−rho], gives

    ||mean_K F||≤C sqrt(Delta)rho^(−(p+1)/2)+C rho².

The same estimate on the right calibration interval applies to the second folded branch. These intervals lie in the pole neighborhoods because 2rho≤2r0<4r0, and inside K because 3r0<D. Their normalization is at an exterior pole, not at the initially unprescribed middle residue. The triangle inequality and bounded |K| give (22).

Set h=min(r0,a/4). If 0<Delta≤h^[4(d+9)/3], then rho=Delta^[1/(d+9)]≤h^(4/3)<1 and eta=rho^(3/4)≤h. Hence rho≤eta, rho≤r0 and eta≤a/4. Every needed interval exists on this one scale. With p≤d+4,

    sqrt(Delta)rho^(−(p+1)/2)=rho^((d+8−p)/2)≤rho².

Here the final inequality has this direction because rho<1 and the exponent is at least 2. For the fast profiles the exponent is (m+4)/2, and for coupling it is (m+5)/2. Products e^g M remain uniformly Lipschitz in g and M on the bounded region, yielding all of (23), including their union-of-branches norms.

At D the common remainder gives S=B/tau²+O(1), hence P_S=B+O(tau²), uniformly. On [D−2rho,D−rho], (23) and the triangle inequality give sqrt(rho)||B−I||≤C rho²+C rho^(5/2), proving (25). The proof has not inserted B=I into this calculation. The exact consequence in section 2 merely makes the bound nonsharp.

Both values F(D±eta) use the same R_D(D), and the model's finite part at D is zero. Thus (26) is ||B−I||/eta+O(eta) on each side. Unequal branch constants are excluded by the single C^q remainder in the unchanged hypothesis. No identification of unrelated gauges is assumed.

For t∈J_(a/2), integrate on its own branch from D±eta. Each path lies in [a/2,T−a/2], has distance at least eta from D, and is contained in the domains of (23). H'≤K csc²t I is uniformly bounded on these paths. The H error and C' error integrate to C_a rho². For the fast derivative error,

    ||4csc²(2t)||_(L²(path))≤C_a eta^(−3/2),

since its square is O(|t−D|^−4) near D and the exterior pole is bounded away. Cauchy–Schwarz gives C_a rho²eta^(−3/2). The additional LH'L^T term has integral at most C_a||L||_2²≤C_a rho⁴, not merely C rho². Thus every term in (27) is justified.

After eta=rho^(3/4), the powers in (28) are 3/4, 3/4, 7/8, 2 and 4. Their sum is at most C_a rho^(3/4). This is precisely Delta^[3/(4(d+9))], with no unannounced change of time or constants depending on Delta.

## 8. Derivatives, zero defect and shear

Locations: PROOF 271–292, equations (29)–(30); STATEMENT 47–52.

The atlas supplies (29) on the wider set, for the reason in section 2. R_D(D) has norm at most K, and derivatives of this constant vanish. For t∈J_a, q Taylor sample points with step at most a/(2(q−1)) fit into the corresponding wider interval. Solving the fixed Vandermonde system gives C(epsilon h^(−j)+M h^(q−j)). At h=(epsilon/M)^(1/q) this is the product term in (30). If h is capped, M≤epsilon h_cap^(−q), so both terms are bounded by C_a epsilon. If epsilon=0 or M=0, the claim follows by the zero function or a limiting step, with no division problem. This proves the stated form for all integers 0≤j<q; matrix components introduce only dimension constants.

Since Delta<1 and the number of derivative orders is finite, (28)–(30) give one common finite C for all those j, independent of A,B,Delta. No bound for j=q is asserted or obtained by an illicit regularity improvement.

At Delta=0, rho remains an arbitrary positive small number. The variances vanish; calibration gives O(rho²). Choosing eta=rho^(3/4) only after choosing such rho, and letting rho↓0, forces the fixed F to vanish on J_(a/2). Its derivatives vanish there, so the same conclusion holds for all j in the frozen range. The proof never constructs an interval from rho=0.

The map (q,p)↦(q,p−C_*q) is symplectic exactly because C_* is symmetric: the extra bilinear skew term is zero. It sends graph A to graph(A−C_*), fixes the vertical plane, and changes neither A' nor endpoint differences. Therefore it preserves f and Delta exactly. This is the single specified shear on both branches, not an arbitrary symplectic equivalence.

## 9. Nonvacuity and auxiliary geometric baseline

Locations: PROOF 294–307; DERIVATIONS 37–45.

For |epsilon|<1/24, psi'=1+12epsilon sin²(4t)cos(4t)>1/2. The map fixes 0,D,T and is strictly increasing, so it maps each half-period to itself, with psi(t+D)=psi(t)+D. Its first derivatives at the three poles are 1. Its local odd Taylor expansion gives smooth removable pole remainders with identity residues, and the regular H block extends through D. The diagonal velocity is positive, and both normalized velocities extend positively at every pole. On a sufficiently small closed epsilon interval, compactness of these explicit smooth normalized functions yields one finite K for fixed m,k,q. This does not promise nonvacuity for each prescribed K.

The C block is zero and V(t+D)=V(t), so Q(u,u+D)=0 exactly. For x<y, 0<psi(y)−psi(x)<π. The elementary cotangent chord formulas give exactly the displayed f_epsilon with the absolute value on the fast factor, and the slow sine positive. The denominator stays positive. This expression extends continuously to the full square, including cut and pole lines, so hypothesis 5 is verified.

With c=64epsilon, psi=t+c t³+O(t⁵), psi'=1+3c t²+O(t⁴), and sin²t/sin²psi=1−2c t²+O(t⁴). Hence log[psi' sin²t/sin²psi]=c t²+O(t⁴), exactly the coefficient in PROOF 305. For epsilon≠0 the H profile is nonconstant. There is an open set of interior intervals with positive reference density, nonzero profile variance, and positive w; strict Jensen and (8) give Delta>0. The same explicit continuous formula on the compact endpoint square gives Delta_epsilon→0 as epsilon→0. Thus, with one sufficiently large K fixed for a closed epsilon interval, arbitrarily small positive defects enter the stated threshold for any fixed a. These examples change the input chart, not the coordinate freedom in the theorem's conclusion.

For the auxiliary continuity statement, C² convergence of positive smooth metrics on a fixed closed manifold gives C¹ convergence of the exponential maps on fixed compact tangent disks. Taking r<r'<inj(g) supplies a uniform domain margin for the varying metric balls. On that compact bundle, invertibility of the vertical derivative and injectivity of exp_g exclude both singularity and collisions for exp_(g_j): a hypothetical collision subsequence has a limit, and after injectivity forces coincident limit vectors, a uniform local inverse neighborhood excludes the remaining nearby collisions. This proves the lower limit. For the upper limit choose one directional cut time below inj(g)+epsilon/2, extend just beyond it to a strictly nonminimizing segment of length below inj(g)+epsilon, and use convergence of its geodesic and uniform convergence of distances to preserve the positive length-minus-distance gap. No attainment of the infimum is required.

Diameter continuity follows from uniform metric comparability. Consequently the stated C-infinity precompactness modulo diffeomorphisms, with positive smooth limits and fixed diameter, permits the stipulated smooth classification at a limit. A single limit isometry supplies the gauge in the contradiction argument for convergence to its normalized model. This proves only a non-effective modulus in a fixed C^j quotient comparison; no rate, singular/collapsed-limit conclusion, or smooth compactness from finite derivative bounds is asserted. The finite-union-of-compact-smooth-families example fits exactly this scope. These arguments are not used to replace the chart proof.

## 10. Imported operations, remaining obligations and limits

The exact source interfaces independently read are `lag:determinant`, `lag:poles`, `lag:profiles`, `lag:schur`, `lag:block-bounds`, `weighted:scalar`, `weighted:geodesic`, the global comparison, and the concluding classification statement/assembly at pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Their truth is stipulated. The source's scalar lemma already has the required bounded-log-ratio and measurable-weight scope. Its finite-dimensional algebra transports directly to the abstract hypotheses. The candidate proves its uniform quantitative additions from the displayed spectral and atlas bounds rather than transferring geodesic-dependent source constants.

The actual primary logdet line calculation and nonsingular Schur minimization in Boyd–Vandenberghe, seventh printing with corrections (2009), were read; the covariance and strong-convexity estimates were derived above. Kazdan's original bounded-profile exponential/Jensen/cancellation proof was read from the admitted extraction, with its OCR limits recorded separately. No unproved determinant-root exercise is used as proof. The Vandermonde interpolation is supplied directly. No uninspected geometric antecedent is an independent new premise for the abstract theorem.

**Unresolved essential correctness obligations: none.** The B=I consequence and the scalar-normalization shorthand have explicit resolutions above within the unchanged mathematical content. An additional claim that B≠I occurs, or that small global inj/diam defect supplies these chart hypotheses, would not be covered by this verdict.

Independent coverage is narrower than the author's canonical/literature coverage, as detailed in READING-LIMITS.md. There is no exhaustive project-history or worldwide-priority clearance. There is no formal support: my own exact pinned lean/docs/344.md request returned HTTP 404. Artifact identity checks authenticate the inputs and this review; they do not establish mathematical correctness.
