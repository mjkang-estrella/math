# Independent full proof review of O234

Myeongjin Kang; no affiliation. Original review prose CC BY 4.0. Original verifier code MIT. Third-party inputs retain their rights and are private.

**Verdict: PASS_FULL_O234, without required repairs.** The unchanged candidate proves every quantifier of its frozen target, conditional on the stipulated pinned no-outlier pressure theorem. This is a proof verdict only: contribution, formal support, manuscript, release, acceptance and publication remain separate. Campaign count remains ten of twenty. No public upload is authorized or performed.

This reviewer did not author O234. The reviewer authored the separate OA057 candidate; that unrelated role provides no favorable premise for this review. Neither parent preliminary comments nor an author diagnostic nor a contribution judgment was treated as evidence of mathematical correctness.

## 1. Exact object and assumptions

Author directory: `fresh-analytic-discovery-r27`. External output-manifest SHA256: `85f5d443db8ef59498f183cb91018ff067600d6ef2dd6aa9d2dcec0732f8bb3b`. Candidate SHA256: `2f550b13bee014b9b40657b15c06a4fb112b4b732327ee4bd101662d47adbc87`. Frozen scope SHA256: `cfb52e908976e2968bda9404e615cca27ad9c9b7ea5b19b78fb2885b8d22810b`.

These bytes were authenticated before review. The inspected, read-only author verifier passed with 62 payloads, five directories and 23 pinned blobs; the actual all-zero-anchor control failed. Every selected pinned source receipt independently matched the complete 13223-entry preprint tree, whose truncated flag is false. This authenticates inputs, not conclusions.

The theorem permits any deterministic real diagonal spectra uniformly bounded by a finite K, empirical weak limit mu, and largest-eigenvalue limit theta. Necessarily theta is at least the top support edge b. It imposes no smallest-eigenvalue convergence, no bound on the number of bounded lower outliers, and no finite-rank restriction on the upper deviations. Haar matrices may be arbitrarily dependent across dimensions. The pressure uses uniform probability on the cube and energy beta/2 times the quadratic form. The result is expectation and almost-sure convergence, locally uniformly over every beta>=0, to the displayed source entropy functional with the inverse Stieltjes branch capped at beta theta. Atomic laws, point masses, theta=b and beta=0 are retained.

The stipulated source is family234, `invariant-sk.tex`, Theorem `thm:main`, revision fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. It requires both finite-dimensional extreme eigenvalues to converge to the edges of the limiting support. It is invoked only after that condition has been established for each fixed positive spike fraction. Its truth is not audited. The Gaussian recursion, class of fields, overlap-quantile domain, D_p and order of infimum/supremum in the candidate match the actual source exactly. Source `20-field.tex`, Lemma `fld:domain`, supplies S>=0 and S(0)=0; allowing S=+infinity at p=1 causes no problem when comparing the finite infima.

## 2. Convex ordering and lower clipping

For finite N, differentiating the finite partition sum and Haar expectation is legitimate on bounded coordinate neighborhoods. The derivatives are nonnegative and sum to 1/2, since every spin has squared norm N. Convexity of log-sum-exp survives averaging. Permuting spectral axes preserves the Haar law, so the expected pressure f_N is symmetric.

If d' exchanges i and j, gradient monotonicity gives

    0 <= (grad f_N(d)-grad f_N(d'))·(d-d')
       = 2(d_i-d_j)(partial_i f_N(d)-partial_j f_N(d)).

Thus the derivative order matches the eigenvalue order, with equality at ties by symmetry. There is no reversed inequality or unwarranted coordinatewise convexity inference.

For fixed delta>0, the number q_N of coordinates below a-delta is o(N), by the closed-set weak-convergence bound and compact support. Along the simultaneous straight path raising exactly these coordinates to a-delta, every moved coordinate remains below every unmoved coordinate. Each moved derivative is consequently at most 1/[2(N-q_N)]; the sum of all derivatives is 1/2, even if many coordinates tie. The total expected change is at most K q_N/(N-q_N). Subsequent clipping to a costs at most delta/2 in operator norm. Taking N first and then delta to zero proves Lemma1 without any bottom-edge regularity or minimum limit. This does not incorrectly delete positive outliers.

## 3. Exponential concentration and rank thickening

The all-strength concentration input is valid with the stated constants. For fixed symmetric A, comparison along the line segment between orthogonal U,V gives the Frobenius Lipschitz constant ||A|| for normalized pressure: intermediate matrices have norm at most one, and each normalized exponent has gradient norm at most ||A||. The factor 1/2 in the Hamiltonian is canceled by the two differentiated quadratic terms. A reflection commuting with A switches the components of O(N) while preserving the pressure pointwise; for diagonal A it is a spectral-coordinate sign flip. Thus the component means agree.

I read Fan–Wu Section5 and visually inspected its PDF page37. Equation (5.1) has exponent -(N-2)s^2/(8||A||^2), after absorbing beta into A. For N>=4, (N-2)/8>=N/16. Candidate (5), with any larger norm bound L, follows. The concentration part uses neither the small-temperature moment lemmas nor positive variance of the limiting law. Those assumptions belong to the separate thermodynamic calculation. This distinction is load-bearing because the net has exponentially many directions.

For Lemma2, a maximal eta-separated subset of the sphere of the k-dimensional flat block has cardinality at most (1+2/eta)^k by disjoint-ball volume comparison. If v is within eta of y/||y||, then v·y/||y||=1-||v-y/||y||||^2/2>=1-eta. Squaring yields exactly the proposed projection inequality with strength a'=a/(1-eta)^2. The a>=0 condition is retained when applying it to the exponent.

For each spin, exp of the maximum over v is at most the sum over v. Summing the spins therefore proves the actual inequality

    Z(A_0+a Pi_E,U) <= sum_v Z(A_0+a' vv^T,U).

Taking logarithms gives a maximum of the pressures plus log M/N, not an interchange of expectation and logarithm. Rotations inside E fix A_0 because it is scalar there; hence all net pressures have exactly the same Haar mean m'. This would be false on a general nonflat block, and the proof explicitly flattens before using it.

The upper tail of their correlated maximum is bounded by min(1,2M exp[-Ns^2/(16L^2)]). No independence is needed. With q=log(2M)>=log2 and s_0=4L sqrt(q/N), its integral is at most

    (L/sqrt N)(4sqrt q + 2/sqrt q)
    <= 8L sqrt((q+1)/N).

The last loose constant follows, for instance, by squaring or elementary bounds for q>=log2. Integrating only the positive part bounds the expected centered maximum from above even if it can be negative. The a'-a operator-norm cost is exactly (a'-a)/2. The opposite inequality follows from a(Pi_E-v_0v_0^T)>=0. This proves every finite-N claim in Lemma2.

## 4. Transform continuity, cap and zero

For measures supported in [-K,K] and cap t in that interval above the support, H is strictly decreasing and continuous on (t,infinity). The uncapped branch exists exactly when x<H(t+). Its root, or the capped value, lies in [t,t+1/x]. The inequalities H(z)>=1/(z+K) and, when z>K, H(z)<=1/(z-K), give -K<=R<=K on the uncapped branch. On the capped branch x>=H(t+)>=1/(t+K), so R=t-1/x>=-K, while R<=t<=K. If t=-K, the law must be delta_{-K} and H(t+)=infinity: there is no capped branch at finite x, so no division by zero is required.

For x_j->x>0, any root subsequential limit exceeding t satisfies the limiting uncapped equation because its arguments are separated from every support. A hypothetical limit t below the desired root is excluded by choosing one c strictly between them and comparing H_j(c)>x_j. If the desired branch is itself capped, a limit exceeding t would solve an impossible uncapped equation. This covers threshold equality and atoms. The same argument with fixed parameters establishes continuity in x; sequential compactness then gives uniform convergence away from zero.

For x<1/(4K), H(t+)>=1/(2K) excludes capping uniformly. Substituting b=1/x+R into H(b)=x gives

    R(x) = mean(rho) + O(K^2 x),

with a constant uniform over every allowed law and cap, since |x(R-lambda)|<1/2. Bounded weak convergence gives convergence of means. This supplies the missing neighborhood of zero without assumptions on an atom or density at the edge. Taking K larger than zero handles the zero-law case. Finally the uniform R bound controls the spectral functional uniformly over all p because D_p lies in [0,1]. Adding the same extended-real S and taking infima is legitimate; p=0 ensures finiteness. Lemma3 proves precisely the needed continuity even though t need not be a support edge.

## 5. Spectral sandwich and unchanged scope

After lower clipping and sorting, c_i=min(d_i,b) lies in [a,b]. Bounded weak convergence and positive limiting mass in every support-edge neighborhood force its extrema to a,b. If theta=b, operator comparison already finishes the proof; no unnecessary spike argument is used.

For theta>b and fixed epsilon, replacing the top k_N=max(1,floor(epsilon N)) clean coordinates by theta produces B_(N,epsilon). Bounded weak convergence is equivalent to W1 convergence here. The one-dimensional increasing-quantile coupling gives L1 convergence of quantiles, so deleting the top k_N/N mass converges to restriction of Q_mu to (0,1-epsilon). Moving the truncation endpoint by o(1) costs o(1) because the quantiles are uniformly bounded. Hence the law is exactly the candidate's nu_epsilon. This reasoning covers atoms and gaps; continuity at the truncation quantile is unnecessary.

Its bottom support edge remains a: the retained interval has positive length, and every sufficiently small bottom neighborhood contains positive lower-quantile mass. Its upper edge is theta because epsilon>0. The actual B extrema tend to a and equal theta. Thus the no-outlier theorem applies at this fixed epsilon even for a=b. Sending epsilon to zero only afterward gives F(nu_epsilon,theta)->F(mu,theta) by Lemma3.

The first k_N clean coordinates are flattened to b before Lemma2. The rank-one version T differs from S_N=(theta,c_2,...,c_N) by operator norm at most b-c_k. For every delta>0, positive mass in (b-delta,b] implies c_k>b-delta eventually whenever epsilon is sufficiently small. This proves the iterated-limit flattening cost (23), including atoms at b and point masses. Taking eta=sqrt epsilon makes every term in (24) vanish: strength inflation is O(sqrt epsilon), net entropy is O(epsilon log(1/epsilon)), and the maximum cost is O(sqrt(epsilon log(1/epsilon))). All norm constants are uniform for epsilon<1/4.

The source value for B and these two inequalities squeeze S to F(mu,theta). This is N then epsilon, not an assumed uniform source theorem at vanishing atom mass.

For the original lower-clipped spectrum, replacing only the first coordinate by theta costs |d_1-theta|/2; all other coordinates dominate c_i. This gives the lower bound (26). For fixed epsilon, only o(N) eigenvalues exceed b+delta for each delta>0; therefore (d_(k+1)-b)_+->0. The coordinatewise upper bound (27) follows: top k coordinates are at most d_1, and remaining coordinates exceed their clean values by at most that residual. An exact scalar shift changes pressure by half the shift. These inequalities cover even a linear number of tiny edge deviations, as well as every finite or sublinear set of separated upper outliers. Reinstating Lemma1 includes bounded lower outliers with oscillating minima. No unmentioned rank, rate or endpoint assumption is used.

## 6. All temperatures and modes of convergence

For each fixed beta>0, multiplying all spectra by beta preserves every hypothesis, with law beta_*mu and top beta theta. The zero case is identically zero and the functional agrees because R=0 and inf S=0. The deterministic K/2 Lipschitz bound in beta holds for every U,N and for the expectations. Pointwise expectation convergence therefore gives a Lipschitz limiting function and uniform convergence on every compact beta interval by finite meshes.

At each rational positive beta, exponential concentration is summable in N for every positive rational error tolerance. Borel–Cantelli needs no independence across N. The countable intersection produces one event on which all rational temperatures converge; the deterministic Lipschitz bound and finite rational meshes then give convergence for all real beta, locally uniformly. The uniform bound |P_N(beta)|<=BK/2 also justifies the candidate's stronger E sup error convergence on [0,B]. The event need not be common to all deterministic spectral sequences; the frozen theorem does not claim that stronger quantifier.

## 7. Independent rank-one calculation

Let s=beta theta>0 and v_i=sqrt N u_i for the Haar row. The energy is s(v·sigma)^2/(2N). Completing the square in t gives exactly

    Z_N = sqrt(Ns/(2pi)) integral exp[N(-s t^2/2
                         + N^(-1)sum_i log cosh(s t v_i))] dt.

There is no missing N, 1/2 or log2. Normalizing iid Gaussians by their empirical second moment realizes the row. The strong law and the Lipschitz bound for log cosh give compact-uniform convergence of the exponent; the empirical first absolute moment is bounded by one after normalization. The bound -s t^2/2+s|t| supplies Gaussian tails outside |t|>=4, so compact Laplace bounds pass to the whole line, including the critical case. The polynomial Gaussian prefactor contributes o(1) to pressure.

The limit is psi(s)=sup_t{-s t^2/2+E log cosh(s t g)}. It is zero for s<=1 by log cosh x<=x^2/2. For s>1, the second derivative at zero is s(s-1)>0, giving a strictly positive value. Maximizers lie in [-2,2]. The uniform inequality 0<=|x|-log cosh x<=log2 gives psi(s)/s->(E|g|)^2/2=1/pi. The direct cube maximum independently gives theta/pi as well.

The Gaussian construction first proves the marginal limit, hence expectation convergence by 0<=P_N<=s/2. The same concentration then yields almost-sure convergence for any cross-N Haar coupling. For delta_0 the capped transform is (s-1/x)_+; it vanishes on [0,1] when s<=1. Above the threshold, the identity between the full source infimum and psi follows from the proved theorem and the independent rank-one limit. It is not presented as an independent direct optimization of the infinite-dimensional source functional. This distinction is correct.

## 8. Objections, attribution and limits of this verdict

There are no required mathematical repairs. Nonblocking presentation improvements for a later manuscript are to cite the explicit (N-2)/8 concentration exponent, state prominently that the probability-one event is for each fixed deterministic spectral sequence, and keep the scalar-block hypothesis next to every equal-mean assertion. All three points are already valid in the candidate.

The cap is antecedent spherical-integral work; high-temperature outlier results are antecedents; sphere nets, convexity, concentration and quantile coupling are standard. The source already supplies entropy, capped continuity, multiplicity comparison and the no-outlier all-temperature theorem. This review validates the new comparison's mathematical use, not its substantiality. The earlier I149/S149 modulus is technical and assumes support-edge convergence of the finite spectra. It does not by itself imply the rank-one versus positive-fraction quenched comparison. A separate contribution reviewer must decide whether that comparison is sufficiently new or already supplied elsewhere.

Actual reading limits and the bounded primary/history comparisons are recorded separately. The proof is prose, not a Lean theorem. The author finite diagnostics were inspected as a receipt but not executed or used as universal evidence. No upstream consistency audit, exhaustive literature survey, claim of peer-reviewed acceptance, or count change is made.
