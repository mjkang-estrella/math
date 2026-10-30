# Structural220 — independent round-one contribution review

**Role disposition: conditional TECHNICAL, at the entire unchanged submitted scope.** The condition is full correctness of both the entire frozen STATEMENT.md and the entire submitted PROOF.md. **That condition remains UNDISCHARGED in this role.** This is neither a correctness grade nor acceptance, adoption, or a campaign count. Parent alone combines reviews. No peer review or author response was consulted.

The authenticated statement has SHA256 `4c71274685f1401193eccbc7c6997b56d1ca2db88fef14cba159d638260aa35d`; the proof has SHA256 `efd13b45cbf17c3620c6bedc00152b1deb42e7cd6f7d37898019ded5aa6b5775`. I read their complete 54 and 307 byte-parser lines, respectively, including the auxiliary density estimates, shear assertion, zero-defect argument and nonvacuity example. Locations below refer to those unchanged files. The operative comparison does not replace or narrow either document.

The basis for TECHNICAL is a full compatible reduction, not a claim that a previously published theorem has exactly the same wording. Source344 already supplies the simultaneous scalar/matrix setup and all endpoint-order and weight identities. Retaining the discarded slacks, applying quantitative convexity on the compact spectral regions assumed in the statement, expanding the Schur covariance, and calibrating on short endpoint intervals produces the entire asserted estimate. The common finite part is supplied by a particularly strong hypothesis. The explicit powers result from elementary scale costs, detailed below. I find no indispensable nonroutine operation left over in the frozen result after this composition. This judgment does not infer literature priority or exhaustive project clearance from a limited search.

## 1. Paid interfaces and their actual applicability

All operative upstream proofs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` are stipulated true. I independently authenticated all 16 same-title canonical blobs against the complete pinned tree. The actual reading relevant to this role consists of the mathematical interfaces in introduction lines 1–47 and 99–116, all of geometric-inputs, all of lagrangian, all of weighted-comparison, global-comparison except one masked bibliographic line, and the complete Schur-path figure source. File-level reading limits are in LIMITS.md. Hashing the other canonical sections does not count as reading them.

* Source344 `02-lagrangian.tex`, `lag:determinant`, lines 112–191: fixed graph coordinates, positive chart velocity, and the endpoint determinant divided by velocity determinants. The geometric realization here comes from normal Jacobi fields of a normalized intermediate Blaschke manifold. For the nominee, the determinant is a definition and positivity is assumed, so none of the geometric construction must be newly proved.
* `lag:poles`, lines 223–330, and `lag:profiles`, lines 332–390: identity exterior residues, a positive free middle residue, a single smooth remainder across the middle pole, regular H and C, and bounded positive normalized determinant-root profiles. The nominee assumes quantitative matrix spectral bounds and C^q versions of these properties. This strengthens the bounds needed by the comparison; it does not require proving them uniformly for a class of nearly Blaschke metrics.
* `lag:schur`, lines 392–542: the endpoint block congruence, Q exchange, the two exact endpoint square completions, and integration from/to a zero matched pair. They hold for both actual endpoint orders: invertibility, rather than positivity, of the endpoint difference of H is enough in differentiation. The path with i=1,j=0 is explicitly covered. Geometry is used to obtain the cut-pair zero; the nominee assumes that zero directly.
* `lag:block-bounds`, lines 544–657: determinant-root minimization, order monotonicity, and the integral determinant-root inequality. These are finite-dimensional positive-matrix operations valid for every positive block size. They do not restrict m,k to the CROSS multiplicities in the geometric table.
* `03-weighted-comparison.tex`, `weighted:scalar`, lines 25–124: the exact logarithmic cancellation for b>0, p_b=(pi/b)^2 csc²(pi t/b), bounded log(p/p_b), and a nonnegative symmetric W with W/sin(pi z/b) bounded. Lines 145–334 prove absolute integrability, folded row AND column balance, coverage of the square by eight triangles, and the strict gap Phi(r)=r−1−log r. The equality conclusion f=w follows from nonnegativity and continuity. These are the relevant abstract operations, not just the headline volume comparison.
* `04-global-comparison.tex`, lines 20–43 and 45–106: polar integration, Liouville invariance, integrated defect 2TV(V−V0), and equality through harmonicity and the stipulated compact simply connected harmonic classification. These require an actual closed smooth Riemannian Blaschke manifold and its invariant measure. They are paid, but are not applied to the arbitrary matrix charts in this review. Classification alone would not prove the positive-defect chart conclusion.

The original primary mechanisms were read, with the qualifications below. Kazdan's Appendix E, E.4–E.16, writes the functional as an exponential of u(x)+u(y)−2u(t), applies Jensen, and proves the linear term cancels precisely for a symmetric weight. The finite-endpoint subclass and the mathematical added-in-proof equality note were read separately. Under phi=sin(t)e^u, g=−2u and rho=W/sin(t), this is the scalar operation used by Source344. It is not an unrestricted matrix stability theorem.

Berger (1980), theorem, Lemmas 1–2, integrated proof and equality paragraphs, combines disjoint geodesic balls, flow-invariant integration, paired t and pi−t weights, the main weighted inequality, and equality in Jensen. Its domain is compact Riemannian geometry with an injectivity-radius lower bound, normalized there to pi; its conclusion is a volume bound with a spherical equality case. The separate 1977 intermediate “Main Inequality” paper was not read; here its relevant stronger chart operation is available in the stipulated source, and the scalar operation is read in Kazdan. Berger is not used as if it already had the nominee's matrix-chart topology or rate.

Rovenskii–Toponogov (1996 v1), Theorem 26 and the complete calculation through its final beta formula, was read. F1 requires a totally geodesic round sphere S^a(4) through each direction, with a=2,4,8 and the stated dimension restriction at a=8; F2 controls intersections of those spheres. In the proof these assumptions give a curvature-invariant tangential block with explicit Jacobi factor (sin 2t)/2 and a complementary determinant. Hölder, the scalar interval inequality, Kazdan's weighted cancellation, and global volume integration then give the volume comparison and equality. Neither F1/F2 nor their curvature splitting is available for arbitrary charts. Source344's fixed-chart Schur factorization is the stronger compatible paid replacement; there is no illicit removal of F1/F2 from the old geometric theorem.

Boyd–Vandenberghe, the author-hosted seventh printing with corrections (2009), was read at the actual logdet line proof in §3.1.5 and the nonsingular Schur minimization in §A.5.5. The first gives the Hessian of −logdet; the second minimizes a positive quadratic block and identifies its Schur complement. The quantitative constants and the integrated covariance below follow directly from those operations. I do not count the determinant-root exercise as a proved primary theorem. No quantitative geometric rigidity theorem, diffeomorphism theorem, compactness rate, or unseen intermediate proof is needed in the reduction.

## 2. Compatible reduction through the entire result

The following is an independent contribution comparison written at the supplied hypotheses, conditional as stated above. It retains the exact theorem, including arbitrary m,k≥1, integer q≥2, K≥1, 0<a<D/2, free B, the specified C_*, the displayed threshold and the zero-defect clause. Constants c,C below depend only on m,k,q,K,a as appropriate; fixed T=pi, D=pi/2 and r0=pi/64 are numerical constants. No constant depends on A,B,rho,eta or Delta. If a given small K makes the admissible class empty, the uniform assertion for that K is simply conditional on admissibility; nonvacuity does not claim examples for every K.

### 2.1 Keep every nonnegative source remainder

Set h0=csc²t, p0=4csc²(2t), h=det(H')^(1/m), s_i=det(S(t+iD))^(1/k), g_H=log(h/h0), g_i=log(s_i/p0). Normalize M_H=H'/h and M_i=S_i/s_i. Hypothesis 2 implies |g|≤log K, det M=1, and spectra in [K^−2,K²]. These bounds are uniform even at the level of arbitrary m,k. Hypothesis 1 makes H strictly increasing through D, so the endpoint Schur calculation is applicable also across D.

For a positive r by r profile P, let p=det(P)^(1/r), a_xy=integral_x^y p, and

    D_P = log det(integral_x^y P) − r log a_xy
        = log det E_mu(P/p),       dmu=p dt/a_xy.

Concavity of logdet and det(P/p)=1 give D_P≥0. For 0<u<v<D put I_i=integral_u^v S_i and

    E_ij = log det Q(u+iD,v+jD) − (log det I_i + log det I_j)/2.

The source's two endpoint integrations give Q_ij≥I_i and Q_ij≥I_j, hence E_ij≥0. This includes the reversed actual endpoint order (1,0). Thus no cancellation between errors is required.

For a probability measure nu_xy=p_b dt/integral_x^y p_b write J_b(g)=log E_nu e^g−E_nu g. Define W_D=(sin^m z+cos^m z)(sin(2z)/2)^k and the four weights w_ij=(sin(2z)/2)^k times the matrix with sin^m z on its diagonal and cos^m z off it. Both row and column sums are W_D. They are symmetric on the half period; w/sin z and W_D/sin(2z) are bounded for every m,k≥1, including k=1.

Undoing each discarded inequality in the source gives exactly the following bookkeeping, with Delta_b={0<x<y<b}:

    Delta = 2m integral_Delta_T w J_T(g_H)
          + 2 integral_Delta_T w D_H
          + 2k sum_i integral_Delta_D W_D J_D(g_i)
          + 2 sum_i integral_Delta_D W_D D_i
          + 2 sum_ij integral_Delta_D w_ij E_ij
          + integral_square w Phi(f/w).

Indeed log f_H equals its scalar interval term plus D_H; log f_K equals E_ij+(D_i+D_j)/2 plus k/2 times the two scalar interval logarithms minus endpoint g terms. Row/column summation supplies each D_i once before the endpoint-exchange factor 2, and supplies k times each scalar cancellation. This verifies the coefficients rather than treating “slack retention” as a slogan. The eight folded triangles have Jacobian one and cover the square away from finitely many lines. The bounded profiles bound negative logarithmic parts uniformly; w log^+(f/w)≤f and continuity of f on the entire compact square supply integrability. Thus the formula has finite terms, not an infinite subtraction. It gives Delta≥0.

The auxiliary density claims in PROOF lines 104–109 are also paid by this identity: Phi(r)≥(sqrt r−1)² and Cauchy–Schwarz give integral(sqrt f−sqrt w)²≤Delta and integral|f−w|≤sqrt(Delta(4 integral w+2Delta)). These scalar claims are not used as a substitute for the following matrix estimates.

### 2.2 Uniform quantitative convexity and the localization costs

For |g|≤log K, tilt nu by e^(sg)/E e^(sg). Its density relative to nu is ≥K^−2 for 0≤s≤1. Variance is an infimum over constants, so differentiating log E e^(sg) twice and integrating with weight 1−s gives

    J_b(g) ≥ (1/(2K²)) Var_nu(g).

For matrices N with eigenvalues ≤K² the Hessian of −logdet is

    tr(Z^−1 U Z^−1 U) ≥ K^−4 ||U||_F².

Taylor expansion about E_mu N cancels the linear term on averaging. Consequently D_P≥(1/(2K^4)) E_mu||N−E_mu N||². This is the classical uniform quantitative Jensen mechanism, not an additional matrix theorem.

Choose x∈[rho/4,rho/2], y∈[b−rho/2,b−rho/4], and K_b=[rho,b−rho], for b=T or D and 0<rho≤r0. The rectangle area is rho²/16. The chord integral is ≤8/rho, while p_b≥(pi/b)², so dnu/dt≥c rho on K_b. The actual matrix probability densities are at least K^−2 times the reference density. The independent-copy variance identity gives

    Var_mu(F) ≥ c rho² integral_K_b ||F−mean_K_b F||²,

because the length of K_b is bounded below uniformly. On the T rectangle, T−(y−x)∈[rho/2,rho], so w≥(rho/pi)^d. On the D rectangle, W_D and each same-half w_ii are ≥2^(−m/2)(rho/pi)^k. Keeping the first four terms of the decomposition therefore gives

    integral_K_T ||F−mean F||² ≤ C Delta rho^(−d−4),
       F=g_H or M_H−I;
    integral_K_D ||F−mean F||² ≤ C Delta rho^(−k−4),
       F=g_i or M_i−I, for i=0,1.

The powers are fully accounted for: weight d or k, rectangle area 2, and two restricted probability densities 2. These are deliberately nonoptimal uniform bounds. No local lower bound for a vanishing weight on the entire square has been assumed.

### 2.3 Recover the coupling, not only determinant roots

Put L=C'(H')^−1. On an interval contained in a single branch, let P=integral H', X=integral C' and Lbar=XP^−1. Expanding the quadratic expression with the order of multiplication retained gives

    integral (L−Lbar) H' (L−Lbar)^T
       = integral L H' L^T − X P^−1 X^T
       = Q − integral S.

The cross terms cancel because integral LH'=X=Lbar P. This is exactly the integrated Schur minimization/covariance operation and works for noncommuting matrices. It supplies the information absent from scalar density stability.

On a same-half rectangle, the two relevant pole expansions bound ||V(x)||+||V(y)||≤C/rho. Positivity of Delta H yields 0<Q≤V(y)−V(x), hence lambda_max Q≤C/rho. Write R=Q−integral S≥0. Along integral S+tR≤Q,

    E_ii = integral_0^1 tr((integral S+tR)^−1 R) dt
         ≥ c rho tr R
         ≥ c rho integral_K_D ||L_i−mean_K_D L_i||²,

using H'≥K^−1 I and minimization over constants after restriction to K_D. Integrating with the rectangle weight yields

    integral_K_D ||L_i−mean L_i||² ≤ C Delta rho^(−k−3).

Thus the third error is controlled, with one density/spectral power rather than the two variance-density powers. Both branches are included, and the estimate has not identified two different weighted means.

### 2.4 Exterior normalization fixes the unknown constants

The finite atlas in hypothesis 3 covers I. In particular C' is bounded uniformly on all of I, and (H')^−1≤K sin²t I. Define P_H=sin²t H', P_S=sin²(2t)S/4. Differentiating the exterior expansions gives, with distance t to zero or tau=T−t to T,

    P_H=I+O(t²), P_S=I+O(t²), L=O(t²)

and the analogous O(tau²) bounds at T. Determinant roots, normalized matrices and their logarithms are uniformly Lipschitz on the relevant compact positive spectral set. Thus the g and M−I errors have those same second-order endpoint bounds. For g_H,M_H use the left exterior pole; for the first fast/coupling profiles use zero; for the second profiles use T. No normalization at the unknown middle residue has been presupposed.

For any of these F, if its variance on K_b is ≤C Delta rho^−p, averaging on a calibrating interval of length rho, where |F|≤C rho², gives

    |mean_K_b F| ≤ C sqrt(Delta) rho^(−(p+1)/2)+C rho²,
    ||F||_L2(K_b) ≤ C sqrt(Delta) rho^(−(p+1)/2)+C rho².

The additional half power is the exact cost of calibrating an unknown constant on a short interval. The largest p is d+4. Put rho=Delta^(1/(d+9)) when Delta>0. Then sqrt(Delta)rho^(−(d+5)/2)=rho², and all other exponents are at least two because m≥1. Multiplying e^g M on bounded spectral regions yields simultaneously

    ||P_H−I||_L2([rho,T−rho]) ≤ C rho²,
    ||P_S−I||_L2(both branches trimmed by rho) ≤ C rho²,
    ||L||_L2(both branches trimmed by rho) ≤ C rho².

This executes the calibration step rather than assuming that variance controls the distance to the prescribed identity matrix.

### 2.5 Free middle residue and the one specified shear

At t=D+tau, bounded remainders and the inverse H' give S=B/tau²+O(1), so P_S=B+O(tau²), uniformly in B under its stipulated spectral bound. The last normalized estimate for P_S on [D−2rho,D−rho] implies

    ||B−I|| ≤ C rho^−1/2 rho²+C rho² ≤ C rho^(3/2).

No assumption B=I was added. Set F=A−A_mod−R_D(D). The two middle expansions, with the SAME R_D, give at both signs

    ||F(D±eta)|| ≤ C (||B−I||/eta+eta).

The finite part of A_mod at D is zero. Thus the specified shear is forced by the available normalization; a separate choice of gauges, transition map, or topological matching argument is not necessary.

For t∈J_(a/2), integrate F' from D±eta in its own half period. When eta≤a/4 and eta≥rho, all paths lie in the domains of the normalized L² estimates and stay away from the exterior poles. There h0 is bounded by C_a; integral_path p0²≤C_a eta^−3. The block identities H'=h0P_H, C'=LH', V'=p0P_S+LH'L^T then give

    integral ||H'−H'_mod|| ≤ C_a rho²,
    integral ||C'|| ≤ C_a rho²,
    integral ||V'−V'_mod|| ≤ C_a(rho² eta^−3/2+rho^4).

Choose eta=rho^(3/4). Combining the estimates gives

    ||F||_C0(J_(a/2))
      ≤ C_a(rho^(3/2)/eta+eta+rho² eta^−3/2+rho²+rho^4)
      ≤ C_a rho^(3/4) = C_a Delta^[3/(4(d+9))].

The exponents of the first three terms are 3/4,3/4,7/8; the other terms are smaller for rho<1. The exact threshold Delta≤(min{r0,a/4})^[4(d+9)/3] ensures eta≤min{r0,a/4}, rho≤eta, rho≤r0 and all required intervals and paths. There is no chart-dependent threshold hidden in this choice.

### 2.6 Every derivative, zero defect, shear invariance and examples

The same finite atlas supplies a uniform C^q bound for F on J_(a/2): differentiate the explicit pole terms up to order q away from their poles and use the three remainder and two interior bounds. B≤KI and ||R_D(D)||≤K keep this uniform. A finite-point Taylor/Vandermonde interpolation on each narrower component gives

    ||F^(j)||_C0(J_a) ≤ C_a(epsilon^(1−j/q) M^(j/q)+epsilon),
    epsilon=||F||_C0(J_(a/2)), M=||F||_Cq(J_(a/2)), 0≤j<q.

One chooses the sample spacing (epsilon/M)^(1/q), capped by a fixed fraction of the interval margin. The cap yields the additive epsilon term; taking the maximum over the finite j range gives one C(m,k,q,K,a). Since Delta<1, the result is exactly C Delta^[3(1−j/q)/(4(d+9))]. This proves no extra regularity and imposes no bound on derivatives of order q+1.

For Delta=0 the variance estimates hold at every small rho. Calibration gives O(rho²), the residue step gives O(rho^(3/2)), and the matching estimate tends to zero with eta=rho^(3/4). Thus F vanishes on every fixed interior component, and its derivatives vanish there. This is a direct zero-defect argument, not a choice of rho=0 in an inadmissible rectangle. The shear (q_coord,p_coord)↦(q_coord,p_coord−C_*q_coord) is symplectic because C_* is symmetric; endpoint differences and A' are unchanged. The specified shear is the same on both components and no time reparametrization appears in the estimate.

The auxiliary nonvacuity construction in PROOF lines 294–305 is consistent with this comparison: psi_epsilon=t+epsilon sin³(4t) is strictly increasing for |epsilon|<1/24, has psi(t+D)=psi(t)+D and derivative one at the three poles. Substitution into the two scalar cotangents gives exact cut pairs and smooth remainders with identity residues. On a fixed small epsilon interval all required bounds hold for some finite K depending on m,k,q and that interval. Its continuous determinant density is the displayed pullback expression; the H logarithmic profile has nonzero quadratic coefficient 64epsilon, hence a strict scalar Jensen gap for epsilon≠0. Smooth dependence also gives Delta→0 as epsilon→0, so the positive small-defect regime is not merely formal. These are examples inside the admitted abstract class, not a reparametrization allowed in the theorem's conclusion and not asserted Jacobi charts of new Blaschke metrics.

## 3. Contribution objections and possible responses

1. **“The retained full remainder is a new matrix operation.”** Relevant locations: PROOF lines 27–100, 113–124, 164–195; COMPARISON lines 15–17. The exact source endpoint squares and folded cancellations already coexist in the same proof and coordinates. D_H,D_i,E_ij are simply the nonnegative quantities discarded there. The covariance identity is the integrated Schur minimization with its cross terms explicitly canceled. A response pointing out that scalar density estimates fail does not answer this stronger construction. The objection to substantiality is resolved by the compatible derivation above without any change to submitted mathematical content.

2. **“The free residue and common shear are an indispensable new bridge.”** Locations: STATEMENT lines 19–25, 42, 52; PROOF lines 197–269. They are essential conclusions, but the stated exterior identity residues fix the constants in the variance estimates, and a length-rho average near D controls B. The single C^q R_D already identifies the finite parts on the two branches. Taylor expansion and one scale balance give the prescribed shear. A response based on independent local gauges would address a weaker route, not this one. No hypothesis was strengthened and no separate gauge was substituted.

3. **“The explicit rate for arbitrary m,k,q is beyond classification.”** Locations: STATEMENT lines 5, 44–50; PROOF lines 126–160, 218–228, 271–290. Correct as a distinction from classification alone, but not enough for substantiality. The full dependence is accounted for by rectangle powers d+4,k+4,k+3, one calibration half power, the residue average, eta=rho^(3/4), and ordinary interpolation. The primary geometric multiplicity restrictions are bypassed by the paid abstract matrix identities already valid in arbitrary positive sizes, not by extending their geometric theorems.

4. **“The proof may be difficult or new in this exact packaging.”** That is compatible with TECHNICAL under the stated acceptance criterion. This review does not allege copying or assert an exact prior theorem. It identifies the supplied uniform hypotheses that make the complete downstream quantitative construction a routine compatible composition. Evidence of a different weaker-hypothesis metric theorem would not change the review of this unchanged submission.

5. **“The bounded search leaves possible precedents unread.”** Yes. This prevents a global novelty certificate, not the displayed reduction. One original-history section on quantitative Jensen was read at exact boundaries; it concerns affine Walsh fields and supplies no endpoint-chart theorem. It is not a premise for the present derivation, and no old target was reopened or regraded. Unread or excluded history cannot be used as a mathematical obstruction or a novelty claim.

No essential contribution-comparison obligation is left unresolved for this conditional TECHNICAL disposition: the reduction covers the entire frozen conclusion and the submitted proof's auxiliary claims. **The essential full-correctness obligation for the ENTIRE unchanged statement AND submitted proof remains UNDISCHARGED here.** I neither import the parent's intake facts as a correctness verdict nor communicate with the correctness reviewer. If an essential correction to the statement or proof is required elsewhere, that changed submission needs its own proper treatment; this review does not silently apply to a replacement, restriction or renamed target.

## 4. Scope and source limits

The dossier uses local admitted primary extracts and the stipulated source, not a worldwide priority search. OCR limitations and the exact recovery of a truncated primary formula are preserved in LIMITS.md. The original non-effective compactness baseline in DERIVATIONS.md was read, including its strong topology and smooth positive limit requirements, but is not a nominee or a quantitative substitute. No effective passage from a small inj/diam defect to exact cut pairs, a controlled atlas or a common middle remainder is proved or frozen. The statement makes those chart properties assumptions. The distinction is central to the contribution judgment.

The exact pinned `lean/docs/344.md` endpoint independently returned HTTP 404 in this review. No formal comparator or formal proof support is claimed. Artifact authentication and copied controls establish selected bytes/modes only and are not mathematical gates. No acceptance or count is assigned.
