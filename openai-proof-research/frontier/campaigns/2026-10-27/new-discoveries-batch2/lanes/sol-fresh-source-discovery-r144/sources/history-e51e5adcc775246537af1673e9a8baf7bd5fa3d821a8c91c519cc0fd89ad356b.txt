# Structural202 independent correctness review, round 1

**Full-scope verdict: PASS.** The submitted proof establishes the entire unchanged frozen statement. I found no essential mathematical gap and require no repair, additional hypothesis, changed constant, restriction of quantifiers, or replacement statement. The expansions below verify steps already present in the submission; they do not silently install a new construction. This is a correctness verdict only. It assigns no contribution grade, acceptance, or count.

The reviewed target is the author's `FROZEN-STATEMENT.md`, 2443 bytes, SHA256 `fbd2600bdc050aac6e4ab130c3d4a35f88db4fa2af26b5e2b163ee922d760433`, mode 0444, with the supplied freeze time 2026-10-23T20:05:41.310326+00:00. The reviewed proof is `AUTHOR-PROOF.md`, 13488 bytes, SHA256 `121ae56cd4b1444ed373549589c3f53a68fc22e9556c2f959a34084bbcc86b80`. References to numbered sections, equations, or lines of the author proof refer to those exact bytes. The author root is `frontier/campaigns/2026-10-14/fresh-structural-discovery-r202/`.

## 1. Scope, evidence, and dependencies

For every finite real r >= 2 and D >= 1, every pair of real Banach spaces X,Y with C_r(X*) <= D, every compact linear T:Y -> X, and every finite-dimensional E subset X, the conclusion provides a separable reflexive real G, injective compact J:G -> X, compact linear U:Y -> G, and a linear contraction i:E -> G. It provides JU=T, Ji=inclusion, ||J|| <= 2 and ||U|| <= 2||T||. On that same G, for every real s>r, it provides

    C_s(G*) <= 48 D H(r,s),
    H(r,s)^s = sum_{k>=1} (1+log_2 k)^s k^(-s/r) < infinity.

All cotype constants here use the real L2 Rademacher convention in the frozen statement. The nonseparable and zero cases, arbitrary finite-dimensional E, both compact factors, the specified constants, and the order of the simultaneous quantifiers are included in this PASS. No AP/BAP, cotype of X or Y, or reflexivity of X or Y is added.

I read the actual full frozen statement, author proof, DERIVATIONS, STANDING, outside REPORT, FINAL, private READINGS, and the two exactly admitted parent files. Parent questions are a checklist, not evidence that any step holds. No peer review, peer status, parent adoption, or shared coordination state was read.

I authenticated all ten canonical blobs independently against the complete `sources/preprints-tree.json`: 13223 entries, 4858136 bytes, SHA256 `eeecc1da49aa02877d137c4fb90339aca460ec27718b623916368bc08dc5e09b`. All nine actual textual canonical files were read completely. The include order is introduction, preliminaries, coefficient, walsh, approximation, consequences, references. There is no additional operative upstream companion identified by these files. The canonical PDF was authenticated, not semantically read; the entire source proof was read in its authenticated TeX. The pin is `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`. Every operative upstream proof at that pin is stipulated true; this review checks applications and new deductions, not upstream truth.

The frozen proof uses the source's `eq:quotient-lift` and the finite enlargement/weighted quotient operations in `lem:compact-domain`. It does not use the source's AP-dependent main theorem as though X or G had AP. Elementary finite-product duality, completeness, finite-dimensional compactness, reflexivity of ell2 sums and quotients, and elementary compactness arguments suffice for the remaining deductions. Primary literature is compared concretely in Section 10; none of its inaccessible or unexamined results is a missing premise of this proof.

## 2. Fixed-length moments and finite enlargement

Write a=1/2-1/r and Delta_m=D m^a for integers m>=1. Since r>=2, the scalar inequality ||b||_2 <= m^a ||b||_r is in the required direction. Applying it to (||x_i*||) proves c_m(X*) <= Delta_m. Delta_m>=1. This is a fixed-length ell2 cotype bound, not a claim that X* has cotype two uniformly in m.

Let Omega_m be the uniform cube {-1,1}^m and

    V_m h = (E epsilon_i h(epsilon))_i.

Its right inverse is W_m(z)(epsilon)=sum_i epsilon_i z_i: independence gives V_m W_m z=z. The bound ||W_m z||_L2 <= sum_i||z_i|| <= sqrt(m)||z||_ell2 proves bounded surjectivity on arbitrary X. No AP, finite rank approximation, or reflexivity is used here.

For finite atomic Omega_m, L2(Omega_m;X)* is isometrically L2(Omega_m;X*) under expectation pairing, and (ell2^m X)*=ell2^m X*. These are finite-product facts, valid even for nonseparable X; no general Bochner-dual representation theorem or Radon-Nikodym assumption is needed. Under these identifications,

    V_m*(x_i*) = sum_i epsilon_i x_i*,
    ||V_m*(x_i*)||_L2 >= Delta_m^(-1)||(x_i*)||_ell2.

Surjectivity identifies the quotient of L2 by ker V_m with ell2^m X. Its quotient norm at z is

    inf_{V_m h=z}||h||
      = sup_{||V_m* theta||<=1}|sum_i theta_i(z_i)|
      <= Delta_m ||z||_ell2.

This is exactly the admitted source interface. An infimum need not be attained. Because Delta_m>0, a unit tuple nevertheless has a lift of norm strictly below 2 Delta_m. The factor two in the author proof therefore legitimately absorbs nonattainment; it does not assert a bounded linear right inverse of norm Delta_m.

For nonzero finite-dimensional F, the unit sphere of ell2^m F is compact. Choose the finite alpha-net specified in author lines 41-49, with 0<alpha<=min(1/2,Delta_m/sqrt(m)). Each chosen net point contributes only 2^m values of one chosen lift. Their span together with F is finite-dimensional. For a unit tuple z and a net point v, add

    epsilon -> sum_i epsilon_i(z_i-v_i).

This lies in F and corrects every moment exactly. Pointwise triangle inequality and scalar Cauchy-Schwarz bound its L2 norm by sqrt(m)||z-v||_ell2 <= Delta_m. Thus the corrected lift has norm below 3 Delta_m, implying the asserted weak bound (2.1). Scaling and the zero lift handle all tuples. If F={0}, there is no unit sphere to net; only the zero tuple occurs, and its zero lift proves the claim directly. The author explicitly handles this case.

At a fixed level l, M_l=2^(2^l) is a finite integer. Taking the span of the chosen finite net-lift value sets for every m<=M_l still yields a finite-dimensional enlargement. The subsequent corrections already lie in E_l, so the wording about lifts for all tuples introduces no uncountable-dimensional span. All spaces carry the inherited X norm; enlarging a range does not change a previous lift estimate. No linear or continuous selector is required.

## 3. The single nested hierarchy and compact quotient

For T nonzero, K=closure(T(B_Y)/||T||) is a compact subset of B_X. For T=0, K={0}. This uses compactness of T on the entire unit ball, not total boundedness of B_Y. Finite eta_l-nets N_l inside K exist with eta_l=2^(-2l-4). The source and target can be nonseparable: compact subsets of a normed space are compact metric spaces, so these nets require no separability assumption on X or Y.

The induction starts with E_0=span(E union N_0). At each step it retains E_l, adds N_(l+1), and supplies all finite-level lifts up to M_l. It follows that every E_l is finite-dimensional, E_l subset E_(l+1), E subset E_0, and N_l subset E_l. These are all the compatibility conditions used later. The hierarchy is chosen once, with no s parameter.

On H=(direct sum E_l)_ell2,

    j(z)=sum_l 2^(-l)z_l,
    sum_l 2^(-l)||z_l|| <= sqrt(4/3)||z||_H.

Thus j is well-defined and bounded. Truncating j after level L gives a finite-rank map with tail norm at most (sum_{l>L}4^(-l))^(1/2), tending to zero. Hence j is compact.

The closedness of ker j follows from boundedness of j. The quotient G=H/ker j is Banach, and J(Qz)=jz is well-defined and injective. Taking the infimum over representatives gives ||J||<=||j||<=sqrt(4/3)<2. Countable ell2 sums of finite-dimensional Banach spaces are separable and reflexive; the closed quotient is also separable and reflexive. There is no inference from type to reflexivity.

For each g in B_G a representative in 2B_H exists by the definition of the quotient norm, including the zero representative when g=0. Consequently J(B_G) subset j(2B_H) is relatively compact. This proves compactness of J itself. The finite-rank truncations of j are not claimed to descend to G, and no AP conclusion about G or norm approximation of J by finite-rank maps is inferred.

The map i(x)=Q(x,0,...) is linear with ||i(x)||<=||x|| and Ji(x)=x, because E subset E_0. Complementability of E is irrelevant. If E is nonzero, Ji=inclusion also makes i injective. This checks every claim of author Section 3.

## 4. Exact kernel identities and the logarithmic loss

For the stated P_L, nesting ensures that sum_{h=0}^L 2^(L-h)z_h is in E_L. More explicitly than (4.1),

    ||P_L z||_H^2
      <= beta_L^2 sum_{h=0}^L||z_h||^2 + sum_{l>L}||z_l||^2
      <= beta_L^2 ||z||_H^2,
    beta_L^2 = sum_{h=0}^L4^(L-h) = (4^(L+1)-1)/3 >= 1.

The last inequality accounts for the untouched tail. The collapse satisfies

    2^(-L) sum_{h=0}^L2^(L-h)z_h = sum_{h=0}^L2^(-h)z_h,

so jP_L=j exactly. Therefore P_Lz-z is in ker j and QP_L=Q. This can be seen directly from the kernel or from injectivity of J, as in the submission. No approximate kernel relation is being used.

Similarly R(z)=(0,2z_0,2z_1,...) is well-defined by nesting, has norm at most 2, and satisfies jR=j, hence QR=Q. These are identities on all of H, not merely on finitely supported vectors; absolute convergence of j justifies the shift and finite regrouping.

The least L with m<=M_L exists. For m=1,2, L=0 and beta_L=1. For m>2, minimality gives log_2 m>2^(L-1), so 2^L<2 log_2 m. Thus for every m>=1,

    beta_L <= 2^(L+1) <= 4(1+log_2 m).

All levels l>=L can lift the chosen length m. There is no error at the first two lengths, at equality m=M_L, or in the tail estimate. P_L is precisely what makes early coordinates compatible with the all-length hierarchy.

## 5. All-tuples lifts in G and cotype of its dual identity

For a fixed finite tuple (g_i) in G, choose representatives z^i with Qz^i=g_i and ||z^i||<=2||g_i||, choosing zero when needed. Set u^i=P_Lz^i. Its coordinates below L vanish. At each l>=L choose the finite-level moment lift h_l of (u_l^i)_i. Only countably many choices are made, with each function defined on the same finite sign cube.

Define v_0=0 and v_(l+1)=2h_l for l>=L, with the intervening coordinates zero. The square-sum estimate is

    E||v||_H^2
      =4 sum_{l>=L}||h_l||_L2^2
      <=36 Delta_m^2 sum_i||P_Lz^i||_H^2
      <=144 Delta_m^2 beta_L^2 sum_i||g_i||_G^2.

The equality and interchange are justified first for finite coordinate truncations and then by the nonnegative series. Since each atom has probability 2^(-m)>0, finiteness of the expectation proves that v(epsilon) is in H at every atom, not just outside an unspecified exceptional set. Finite-sum expectation is continuous on this H-valued finite-product space. Its i-th moment has coordinates (0,2u_0^i,2u_1^i,...), hence equals Ru^i. Therefore

    E epsilon_i Qv = QR P_L z^i = g_i.

This verifies (4.4) and (4.5), including the infinite assembly and the order of taking moments and quotienting.

For any theta_i in G*, the moment identity gives

    sum_i theta_i(g_i)
      = E <Qv(epsilon), sum_i epsilon_i theta_i>.

Cauchy-Schwarz, ||Q||<=1, and the square root of the displayed estimate yield the author's factor 12 Delta_m beta_L. Taking the supremum over sum_i||g_i||^2<=1 gives exactly (sum_i||theta_i||^2)^(1/2). Finite ell2 duality establishes this equality even if the individual functional norms are not attained. Thus

    c_m(G*) <=12 Delta_m beta_L
             <=48 D(1+log_2 m)m^(1/2-1/r).

The factors are: 3 from finite enlargement, 2 from the weighted shift, 2 from quotient representatives, and at most 4(1+log_2 m) from P_L. They multiply to 48(1+log_2 m), with no additional Kahane constant or probability-normalization factor. The source's separate L_infinity lift constant 24 does not enter this L2 construction.

Crucially, this is an estimate for arbitrary tuples of functionals in G*, against the Rademacher norm in G*. It is cotype of the identity of G*, not cotype of J*, U*, or a factor map. Neither cotype passing to quotients nor uniform cotype of the individual E_l* is assumed.

## 6. Rearrangement, the series, and simultaneity

Fix any finite tuple (theta_i) in G*, order its norms a_i decreasingly, and put A=Rad_2(theta_1,...,theta_n). Reordering does not change the sign distribution. Conditional expectation of the full signed sum given its first k signs equals the first-k sum. Convexity of the squared norm gives Rad_2(theta_1,...,theta_k)<=A.

The fixed-length estimate therefore implies

    sqrt(k)a_k <= (sum_{i<=k}a_i^2)^(1/2)
      <=48D(1+log_2 k)k^(1/2-1/r)A,

and hence a_k<=48D(1+log_2 k)k^(-1/r)A. Raising to any real s>r and summing gives exactly C_s(G*)<=48D H(r,s). If A=0, the moments of the signed sum imply every theta_i=0, and the estimate remains valid. Empty tuples are vacuous.

For convergence, choose delta=(s/r-1)/2>0. The logarithmic factor (1+log_2 k)^s is eventually bounded by a constant times k^delta, leaving a scalar power exponent s/r-delta=(s/r+1)/2>1. Thus H(r,s) is finite for each such s. There is no claim of a bound uniform as s decreases to r, and the series used here does not converge at s=r.

The order of quantifiers is correct: the same previously constructed hierarchy, quotient G, and maps J,i,U serve every s>r. Neither s nor a countable choice of exponents is used to build G. This is not a collection of unrelated factorizations G_s.

## 7. Compact lifting without continuous net selections

For each x in K choose v_l(x) in N_l with ||v_l(x)-x||<=eta_l. No continuity is assumed. The proposed representative has

    z(x)_0=v_0(x),
    z(x)_l=2^l(v_l(x)-v_(l-1)(x)), l>=1.

Its l-th coordinate is in E_l by nesting. Since N_0 subset K subset B_X, ||z(x)_0||<=1. For l>=1,

    2^l(eta_l+eta_(l-1))
      =2^l(4^(-l)/16+4^(-(l-1))/16)
      =(5/16)2^(-l).

Consequently

    ||z(x)||_H^2 <=1+(25/256)sum_{l>=1}4^(-l)
                 =1+25/768=793/768<4.

This is the exact stated fraction, not an approximate numerical check. Moreover j(z(x)) telescopes to lim_l v_l(x)=x. Hence K subset range J.

For each fixed coordinate, z(x)_l belongs to a finite set: N_0 for l=0, and 2^l(N_l-N_(l-1)) for l>=1. The sum of the squared coordinate bounds after any cutoff tends uniformly to zero. Given any positive error tolerance, truncate beyond a cutoff making the tail smaller than that tolerance; there are only finitely many truncated vectors. This proves total boundedness of Z_K={z(x):x in K}. Completeness of H makes its closure compact. This argument does not say that Z_K itself is closed, or that x -> z(x) is continuous.

The quotient image Q(Z_K) is relatively compact. Injectivity of J makes Qz(x) the unique lift of x, independent of every net choice. As every point of K has a lift,

    Q(Z_K) = {g in G : Jg in K}.

The right side is closed by continuity of J and closedness of K. Equivalently, the sequence argument in author lines 182-186 gives the same conclusion. Relative compactness plus closedness proves compactness of K_G=J^(-1)(K). Its norm bound is sqrt(793/768). No continuity of the arbitrary representatives, continuity of an inverse on all of range J, or AP is used.

## 8. The operator U and every edge clause

For nonzero T, if y!=0 then Ty is ||T||||y|| times an element of K. Thus the whole range of T lies in the linear range of J. Define U(y) to be the unique g with Jg=Ty. For scalars a,b and y_1,y_2, linearity of T and J gives

    J(aUy_1+bUy_2)=T(ay_1+by_2),

so uniqueness proves linearity of U on all Y. For ||y||<=1, Uy belongs to ||T||K_G. Hence U is bounded with

    ||U|| <=sqrt(793/768)||T|| <2||T||,

and is compact because its entire unit-ball image is contained in a compact set. The identity JU=T follows from the definition.

If T=0, set U=0, as the submission does. The hierarchy can still retain arbitrary E, and all cotype and J estimates remain valid; no division by zero occurs. If E={0}, its contraction is the zero map, and the net-based construction still works. If E_l={0} at a level, the zero version of the enlargement lemma applies. If both E and T vanish, one may use zero nets and zero levels, producing G={0}; unnecessary nonzero choices are not needed. If X={0}, the explicit initial branch gives G={0} and all maps zero, with C_s({0})=0. Y={0} is covered by T=0.

Finite-dimensional endpoints impose no extra difficulty. The construction remains a valid countable ell2 sum and closed quotient, even if the nested subspaces eventually stabilize. Nonseparable endpoints cause no selection, measurability, or reflexivity problem, because only finite-dimensional nets, the compact set K, and countably many finite-dimensional levels are used.

The proof does not assert AP for G or G*, primal cotype for G, K-convexity for G, cotype r for G*, or a complex-field version. None is needed to derive a frozen conclusion. The simultaneous U and i are compatible because they use the same J; if Ty happens to belong to E, uniqueness even gives Uy=i(Ty), with no additional condition.

## 9. Strongest paid source operations and the submitted composition

The full source supplies substantially more than a headline compact-domain lemma. Its preliminaries give probability-normalized finite-product duality, fixed-length cotype amplification, the quotient-lift identity, and bounded L_infinity moment lifts with L=24. Its coefficient lemma concerns binary Fourier-index rank, not operator rank. Under d=ceil(2 log_2 m), 4<=d<m and min(ma,mb)>=80d(d+1)^2, it produces a positive coefficient bound depending only on m,a,b. The growth lemma applies to arbitrary nonzero operators satisfying its fixed-length domain-dual/range moments. Uniform decay then applies to finite-rank operators and their operator-norm closure, with n_0=4m(K_0+2)+2, K_0>log_2(1/c_1), and the displayed decay sequence. The rank-dependent Hilbert factorization is used only to contradict slow decay for one operator.

The source compact-domain proof already supplies finite sphere-net enlargement, the weighted ell2 sum, closed quotient, compact injective J, prescribed E, the exact QR=Q identity, and the dual moment-pairing argument. Its construction also already makes the chosen G separable and reflexive, even though those properties are not the displayed headline. None of those mechanisms should be credited as a newly proved prerequisite here.

The compact-open operator transfer in DERIVATIONS is compatible with the full source. For A:Z->W compact-open approximable by finite-rank maps, with C_r(Z*)<=D and C_q(W)<=C, choose a sufficiently large m and source domain with c_m(G*)<=12D m^(1/2-1/r). The source parameter values are ma=m^(1/r)/(576D), mb=m^(1/q)/(48C). Approximating A on closure(J(B_G)) makes the finite-rank composites converge in norm to AJ. Uniform Walsh decay then transfers back through the contraction on the finite-dimensional input span, giving w_N(A)<=2rho_N||A||. Norms of the original approximants need not be uniformly bounded. AP of either appropriate endpoint supplies this compact-open approximability. This is already a compatible paid consequence and is not an extra premise of the frozen theorem.

For the present target, the full compatible composition is explicit: retain the source's finite lift operation at all m<=M_l in one hierarchy; insert the compact-image nets; use P_L to reach a level permitting the chosen m; use the source's shift/quotient pairing; then use rearrangement and the compact telescope. Sections 2-8 verify this composition, including all constants and uniformities. This review does not label that composition routine or nonroutine; that is the separate contribution question.

## 10. Concrete primary comparison and its limits

### Figiel 1973

I visually read the actual publisher scan, PDF pages 1-9, printed 191-207 through Section 7. In Proposition 3.1, the target is embedded isometrically in C(S); the compact composite is approximable there and factors through the universal C_p. Restriction to a closed subspace whose image lies in the original target supplies two compact factors. Corollary 3.3 chooses 1<p<infinity, making C_p and its closed subspace reflexive. Sections 4-6 give the actual finite-dimensional disjoint-projection and finite-rank decomposition mechanisms behind the universal construction. Section 7's further L_p restrictions were also read. This is proof reading, not the blank pdftotext output.

These operations fully pay for classical compact reflexive factorization. One can strengthen its interfaces in elementary ways: factor an augmented compact operator on Y direct-sum E to include the prescribed subspace, then quotient the kernel of the output map to obtain injectivity. A closed quotient of a reflexive domain remains reflexive, and compactness survives this quotient by bounded representatives. These observations retain E algebraically; they do not by themselves certify the simultaneous frozen norm normalizations. Thus prescribed E and injectivity are not reasons by themselves to dismiss a classical composition. However, the universal C_p includes arbitrary finite-dimensional geometries; it and its dual do not have the needed uniform finite-cotype geometry. No identity estimate on the resulting quotient dual with constant 48D H(r,s) follows from this universal-space choice alone. The moment construction in the submitted proof supplies that missing estimate directly.

### Pisier 1980, 1980-81, and 1983

The actual Pisier 1980 text was read on PDF pages 3-15, including Section 2 through Corollary 2.16; pages 14-15 were also viewed to recover the tensor decomposition and exact compact-open approximation quantifier. Lemma 2.3 already expresses a moment-lift norm as a quotient norm by annihilating higher Walsh moments. Proposition 2.2 combines cotype-two hypotheses with R(u); the later tensor decomposition iterates a small remainder to obtain nuclear control. Corollary 2.16 gives Hilbert factorization for compact-open approximable u when the domain dual and range both have cotype two, with no uniform BAP assumption. This stronger compatible operation is paid. Its hypotheses do not hold automatically for the frozen T:Y->X: neither Y* nor X is assumed cotype two. Applying it to T* does not fix that mismatch.

The suite exposé VII was read visually on all nine mathematical pages, PDF4-12. It proves the stated K-convexity result under 1/q+1/q_*>1/2 and the indicated approximation/complementation hypotheses through Walsh, semigroup, and finite-dimensional estimates; its operator discussion does not assert that an operator estimate is an identity estimate on a factor space. The supporting exposé II duality/semigroup portions were read as recorded privately. In particular, finite dual cotype cannot be converted to primal type here by silently adding K-convexity. The present proof makes no such conversion.

Pisier 1983 was read in the actual text on PDF2-21, with image recovery on PDF12 and17-21. The graph quotient (B direct-sum_1 E)/{(s,-us):s in S} extends a map while retaining E isometrically. For ||u||<=1/[2(K+1)], its proof bounds the new cotype constant by max(c_q(E),2Kc_q(B)), so iteration does not accumulate a multiplicative loss. Concretely, the proof's a,b satisfy a+b<1; the coefficient estimate is bounded by Kc_q(B)a+c_q(E)(b+a/2), which is at most max(c_q(E),2Kc_q(B))(a+b). Theorem 2.4 iterates this extension, and Theorem 3.2 and Remark 3.6 give the actual cotype-two/AP-removal obstruction. No constants from its first-moment convention are transferred to the frozen L2 bound.

This envelope is also a real comparison, not merely an obstruction. Applied to a cotype space such as X*, its extensions go into a larger space; dualizing provides a quotient onto X**, not an automatic compact linear lift of T into a prescribed reflexive predual or a map with range in X. Restriction and quotient choices must still preserve the required identity moments. No such additional claim is imported. The embedded-ell1 example does not contradict the frozen result, which asserts neither primal cotype nor AP/K-convexity of G and does not factor an infinite-dimensional identity as a compact operator.

### Jarchow-Matter 1988

I visually read all twelve original scan pages, printed45-56, including definitions, every supplied proof, (10), (12), (13), and references. In (10), the interpolation couple is (domain/ker T, target), and an intermediate space of both J- and K-type theta factors T. For T* in the present setting, take the ideals A=compact maps and B=compact maps intersect operator-cotype-r maps. Compact maps are closed, injective and surjective; the cotype ideal is injective. T* is compact and has operator cotype r at most D||T||, because X* has cotype r. Thus the construction applies and, for each 0<theta<1, yields T*=R_theta S_theta with both factors compact and S_theta of operator cotype r/theta.

Both compactness assertions deserve payment: A^theta=A follows from the small-error image inclusion and total boundedness; B_(1-theta) subset (compact)_(1-theta)=compact follows from the domination inequality or (5)(c). For the latter, take a bounded sequence with convergent images under the compact dominating map; the interpolation domination makes its images under the new map Cauchy. Thus it would be incorrect to say that this paper controls only one compact factor.

The author's omitted-Hölder comparison in DERIVATIONS lines87-95 is correct. If

    ||Sx||<=c||Ax||^theta||Bx||^(1-theta),

with A of operator cotype r, then

    (sum_i||Sx_i||^(r/theta))^(theta/r)
      <=c(sum_i||Ax_i||^r)^(theta/r)(max_i||Bx_i||)^(1-theta)
      <=c C_r(A)^theta ||B||^(1-theta) Rad_2(x_i).

The last step uses ||x_i||=||E epsilon_i sum_j epsilon_j x_j||<=Rad_2(x_j). The powers of the Rademacher norm add to one. This proves the relevant weakening in (12)(a) directly in the exact L2 convention. No K-convexity hypothesis is needed for this cotype application of (10); the K-convexity requirement in (13) is relevant to its separate type assertion.

I also checked the natural attempts to strengthen this comparison. Dualization gives a compact-factor decomposition of the canonical image of T in X**. Restricting an intermediate dual space to the preimage of X and quotienting the output kernel can handle range and injectivity; Figiel can supply reflexive compact factorizations, and an augmented operator can retain E. These compatible operations still do not turn S_theta's cotype estimate, whose right side is Rad_2 of preimages in X*, into an estimate whose right side is Rad_2 in the intermediate space. Density of a range alone supplies no bounded simultaneous lifts. Renorming a range by a quotient norm is precisely where an additional moment-lifting argument would be needed, rather than an unrestricted claim that cotype passes to quotients. Furthermore (10) chooses its interpolation space using theta; repeating it for different theta does not supply the frozen one-G/all-s assertion or its specified numerical bound.

This analysis does not prove that no other classical combination establishes the full target, and no favorable novelty inference follows from it. The submitted single-hierarchy construction is itself a complete compatible way to resolve these obligations, verified above. Whether that composition warrants any contribution grade is outside this review.

Primary versions and access/reading limits are recorded in `private/primary-authentication.json` and `private/reading-record.json`. Figiel's publisher version is Studia Math.45 (1973), 191ff.; Pisier 1980 is Ann. Sci. ENS13,23-43; the two seminar versions are exposés II and VII, 1980-81; Pisier 1983 is Acta Math.151,181-208; Jarchow-Matter is Note di Matematica8 (1988),45-56, DOI10.1285/i15900932v8n1p45. DFJP and Hinrichs access failures in the author packet are not proof, counterevidence, or novelty evidence. They are not essential dependencies of the frozen proof.

## 11. Formal, history, and artifact boundaries

The actual pinned Lean documentation and indicated `lean/ComparatorChallenges/Cotype.lean` were read in full and independently matched to exact pinned downloads and Git blob hashes. The comparator's `mainTarget_proved` contains `sorry`. It supplies no completed formal coverage for even its declared source target, and none for this frozen factorization theorem. No formalization or compilation was performed. This PASS is a mathematical proof review, not a formal-certification claim.

Only the three admitted original-history spans were read, using binary seek/read before decoding: i88 [1160,6225), i88 [30678,36024), and i90 [26030,34763). They were checked against the author's exact selected copies. Their operative Source326 comparisons distinguish binary Fourier rank from operator rank and compact-composite convergence from BAP. They do not prove the present target or license reopening any historical target. Incidental other-family or disposition prose was not used as a premise. No broad history scan, exhaustive clearance, or world-priority claim is made.

The inspected author verifier was executed read-only with all three supplied detached anchors and accepted 119 selected files. That verifier binds selected file paths, bytes, and file modes; it does not bind directory or outside-file modes. This is an artifact limitation, not a mathematical defect. Before/after records in this review independently bind the exact 119 selected author files and four outside files, including their observed file modes. No author file or mode was changed, and no author packet was resealed. This review's own verifier separately binds its exact file/directory sets and modes with detached FINAL/MANIFEST/outside REPORT anchors. Artifact controls do not serve as mathematical evidence.

**Final correctness disposition: PASS at the entire unchanged scope. Essential objections: none. Essential repairs: none. Unresolved mathematical obligations of the frozen statement: none identified after the full reconstruction.** Literature exhaustiveness and contribution classification remain unclaimed; they do not substitute for, or weaken, the correctness verdict above.
