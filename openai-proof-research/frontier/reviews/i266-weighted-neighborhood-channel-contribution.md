# I266 independent contribution review of I264

**Verdict: TECHNICAL.** The authenticated target gives a genuine strengthening of the earlier scope, but the full weighted-neighborhood conclusion has a short direct route from the stipulated scalar gap, soliton factorization and matrix LT exponent family. This is not a KNOWN verdict, a proof rejection, or a PASS of I264's displayed proof. No exact published duplicate was established.

Target: `frontier/iterations/i264-weighted-neighborhood-channel-stability.md`, SHA256 `a0080234eacf4d410917e426222e3e89b24f9eba968cc815c4b46c5b59957395`, read in full and authenticated. The complete I264 analysis, including its analytic core/tail defect examples, read log, literature and authentication record were read. The completed I261 review and its complete analysis/read log/literature were read. I265 is live and was not read or consulted. I260's stated PASS on I262 is not transferred to I264. I250/I259/I262/I264 are one chain; this review changes no count and nominates no second spectral finding. The user goal remains twenty total substantial findings, ten accepted.

## Scope actually assessed

Fix a>0 and 1/2<gamma<3/2. For every finite m>=2 and every measurable real unit field v, keep the target-gamma scalar soliton w and normalized ground state phi fixed. Set P=vv^T,

    J=inf_(|e|=1) integral w phi^2 [1-(v dot e)^2],
    D=C_gamma integral w^(gamma+1/2)-Tr(-d^2 I_m-wP)_-^gamma.

The proposed conclusion is c_-J<=D<=c_+J whenever J<=tau, with explicit positive constants depending only on a,gamma. There is no pointwise orientation, support, derivative or variation condition. The infimum defining J optimizes a constant channel, not a spatial gauge. Small D is not assumed to imply small J; arbitrary profiles, several occupied channels, endpoints and all J globally are outside the statement.

This is genuinely different from essential-supremum-small I262. The discontinuous field e2 on a shrinking interval and e1 outside it has J tending to zero while its supremum distance from every constant projector stays bounded away from zero. The same holds for a fixed-length orthogonal defect sent into the soliton tail. The latter has J of order exp(-2a(r+1)L), not a small orientation amplitude. These examples and their full analytic derivation were read; no numerical validation was substituted. This review judges that larger nonlinear scope, not only a smooth Hessian or the individual named ingredients.

## Explicit response to I261's decisive objection

I261 judged I262 TECHNICAL for this concrete reason. With p=gamma+1/2, M=||f||_infinity and compressed potential U_f=B_w w ff^T, the stipulated SAME-EXPONENT matrix theorem gives

    S_gamma<=C_gamma B_w^p integral w^p |f|^(2p)
           <=N_LT M^(2gamma-1)J,
    N_LT=C_gamma B_w^p w0^(1/r)/c^2.

Because M is small in I262, that bound alone absorbs the entire extra spectral tail at an altered radius. HLW improves its amplitude rate but is not indispensable to comparability. The covariance centering, factorization and local perturbation were judged a useful technical synthesis; no exact published duplicate or proof defect was found. None of that objection is withdrawn or weakened here.

I264 correctly defeats its SAME-exponent absorption step. M can equal one for every positive J. For indicator defects, integral w^p |f|^(2p)=(w0^(1/r)/c^2)J exactly, so merely decreasing J cannot improve the coefficient. One cannot invoke I261's original argument to dismiss I264. The new scope was authored before I261 finished, not as an author rebuttal; the assessment here nevertheless incorporates the completed objection.

There is, however, another direct route. It handles both the nonlinear ground-state loss and the full spectral tail without the proposed small-angle replacement machinery or HLW. Its complete derivation, hypotheses and explicit alternate radius are in `frontier/experiments/i266_weighted_neighborhood_channel_contribution/analysis.md`.

## A direct nonlinear ground-energy comparison

The stipulated equality companion gives h=-d^2-w a simple eigenvalue -a^2 with eigenfunction phi and nonnegative spectrum on phi-perp. For any normalized vector trial function write

    u=phi b+xi,   integral phi xi=0,
    |b|^2+||xi||_2^2=1.

Let E=sum_i q_(h+a^2)[xi_i] and F=integral w|(I-P)u|^2. Both are nonnegative and

    R=q_(H+a^2)[u]=E+F,   E>=a^2||xi||_2^2.

The definition of J applies to every constant vector b, while w<=(r+1)a^2. Thus the triangle inequality and Cauchy--Schwarz give

    sqrt(J)|b|<=sqrt(F)+sqrt(r+1)sqrt(E),
    J|b|^2<=(r+2)R.

Since |b|^2>=1-R/a^2, taking the variational infimum and testing phi e give the exact comparison

    J/(r+2+J/a^2)<=inf spec(H)+a^2<=J.               (1)

For small J the infimum is an actual negative eigenvalue and delta=lambda_1+a^2>=J/(r+3). This argument uses a projection onto phi in every channel, rather than the single occupied channel of I264's H0. It includes all nonlinear orientation couplings through the exact positive term F. In particular it does not discard Q(w|f|^2 phi), expand sqrt(1-|f|^2), require centering of g, or need integral w/rho to convert J into an L1 perturbation size. It is valid for every measurable orientation, independently of m, even before imposing small J.

The new weak-neighborhood eigenvalue burden is therefore paid by a standard gap-and-projection comparison, not by an assumed extension of a scalar published stability theorem. This is a positive derivation covering the actual new hypothesis; it does not rely on calling weighted smallness equivalent to supremum smallness.

## Lower-exponent matrix LT closes the full tail

The elementary partner-factorization estimate q_h[t]>=c_w integral w|t|^2 on phi-perp and Young's inequality give I264's compression to K_f=-d^2 I_(m-1)-B_w w ff^T. The read factorization supplies an independent two-line derivation of this estimate in analysis.md. Interlacing then bounds every moment after the first by K_f's moments. No finite eigenvalue-count assumption is needed.

Set kappa=w0^(1/r)/c^2 and choose

    beta=(gamma-1/2)/(2(gamma+1/2))=1/[2(r+1)],
    s=(1/2+gamma/(gamma+1/2))/2,
    alpha=s(1+beta)/gamma,
    d=[s+1/2-alpha(gamma+1/2)]/(1-alpha).

These choices satisfy 1/2<s<gamma and 0<alpha<(s+1/2)/(gamma+1/2)<1, so d>0 and I_d=integral w^d is finite and explicit. Since y=|f|^2<=1 and integral w^p y=kappa J, weighted Hölder gives

    integral w^(s+1/2)y^(s+1/2)
      <=(kappa J)^alpha I_d^(1-alpha).

Apply the stipulated matrix theorem at exponent s, not at gamma. Its potential may be arbitrary and need not be an optimizer at s. Passing from its s-moment to the gamma-moment with the elementary sequence inequality gives

    S_gamma<=A_tail J^(1+beta),
    A_tail=[C_s B_w^(s+1/2) kappa^alpha I_d^(1-alpha)]^(gamma/s).

The theorem is dimension independent; U_f meets every integrability and measurability hypothesis. This is o(J) with exactly I264's claimed power, even when M=1. The entire open exponent family is an available stipulated input. Restricting the comparison to the single target exponent would artificially remove that resource.

Combine this estimate with (1) and scalar saturation. For an explicit changed radius,

    D>=[m_gamma/(r+3)-A_tail J^beta]J,
    D<=M_gamma J.

For example tau_alt=min{Z/4,a^2/8,[m_gamma/(2(r+3)A_tail)]^(1/beta)} gives the same stated c_-=m_gamma/[4(r+2)] and c_+=M_gamma. This does not validate I264's particular tau. It supplies a direct route to its actual comparability conclusion and the same threshold power. Analysis.md also shows that the exponent-family route supplies any fixed beta'<(gamma-1/2)/(gamma+1/2), so the present intermediate power alone is not a separating consequence.

## Primary overlap and literature limits

The actual pinned equality manuscript and matrix companion were fetched from raw URLs at `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb`, matched against authenticated I261 byte hashes, and read in the extents listed below. They are treated as true, not audited. The equality main theorem classifies constant-unitary direct sums of solitons. Its quantitative action theorem retains auxiliary defects but does not state D comparable to this physical J. The compactness passage contains physical-dimension factors and an equality-limit argument; it is not itself the requested dimension-uniform stability theorem. Its rigidity proof supplies exactly the scalar factorization and gap used in (1).

The matrix main theorem is explicitly quantified over every open-range exponent and every finite dimension, and its read spectral proof handles the full eigenvalue list by exhaustion. Its action and field proofs contain no weighted orientation-deficit corollary. Consequently I264 is not a literal already-stated theorem of those manuscripts. Nevertheless their exponent family and scalar gap imply the conclusion by the explicit comparisons above. No sharp matrix constant is needed for the effective tail beyond a finite dimension-independent constant at s; the target sharp constant and scalar equality are needed for D's normalization.

[Carlen–Frank–Lieb](https://arxiv.org/html/1301.5032v2), Sections 1–2 and all of Section 5, were freshly read with intact mathematical text. Their Theorem 2.2 is scalar lowest-eigenvalue stability, and Theorem 5.1 concerns scalar GNS stability. They give credited methodological prior art, not a published theorem of matrix orientation/full-sum comparability. Replacing wP by its norm w loses all orientation information. Even an assumed vector extension of scalar ground-state stability would still require control of the extra negative moments.

I261's fully read primary notes and authentication records for [HLW](https://www.ma.imperial.ac.uk/~alaptev/Papers/hlw.pdf), [Leng](https://arxiv.org/html/2606.03749) and [Frank–Gontier–Lewin](https://arxiv.org/pdf/2109.05984) were read as inherited comparison records. Their original texts were not freshly reread by I266; their earlier exact extents are preserved in literature.md. No new claim about their unread portions is made. The alternate closure above does not rely on them. The endpoint input in I264 remains credited classical mathematics.

Six bounded current searches were performed. No directly applicable published matrix/vector stability contract was authenticated from those results. This is a search limit, not evidence of novelty or absence. No generic abstract published theorem is assumed. The elementary variational comparison is the review's own derivation from the actually read stipulated contracts. Full-paper reading, exhaustive priority and optimum constants are not claimed.

## Why TECHNICAL, and meaningful repairs

I264's enlarged rough-orientation class is useful. Its explicit nonlinear Feshbach treatment, favorable large-angle term and second interpolation are legitimate proposed responses to difficulties in its chosen proof. But the nonlinear obstacle disappears under the exact h I_m comparison (1); the threshold obstacle is handled by the already available theorem at s plus weighted Hölder. This demonstrates a concise route to the entire new scope, not merely a list of classical ingredients. It supports TECHNICAL under the requested substantial-increment gate.

The substantial general stability barrier remains unpaid: deriving closeness from a small full spectral deficit to the matrix optimizer manifold when profiles, scales, centers and occupied channels may vary. I264 presupposes weighted transverse closeness to one fixed scalar profile. Those broader issues are outside its theorem, and their absence is not a correctness objection. The reason to withhold SUBSTANTIAL here is the concrete closure of the scope actually claimed; the broader barrier explains what substantive stability problem that closure leaves untouched.

Meaningful presentation repairs are to retain the genuinely wider J-only hypothesis, state this as an explicit fixed-profile orientation corollary, and simplify the ground-energy proof using (1). Credit the stipulated exponent family as a second full-tail route and do not describe HLW as indispensable to comparability or to the stated power. If a stronger threshold consequence is intended as the contribution, it must be distinguished from the lower-exponent comparison and supported by an independent sharpness or separating consequence; relabeling the current intermediate estimate does not suffice. None of these suggestions authorizes a scope change, new candidate, count increment or separate finding in this review.

No full proof verdict on the authenticated I264 is issued. In particular this review neither accepts its exact radius and all form/Feshbach constants nor relies on the mere existence of its draft as evidence of proof PASS. I265 remains separate. Read extents, retrieval/extraction failures and detached hashes are in the assigned I266 experiment and literature files.
