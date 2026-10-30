# Three retired statements; no fresh source resolution

Research performed 2026-10-30 UTC, solo, assigned lane only. No children, Lean, manuscript, repository network requests, shared edits, count edits, messages, posting or uploads. Scientific originality is not claimed for any mathematics below.

## Early qualification and selection

Read ancestor and batch AGENTS, current NEXT and both JSON ledgers. Their lane-local context copies are administrative snapshots, not immutable scientific originals. Counts9additional/39total,next40 are context only.

history-receipt.json unions qualified r170/r173/r174/r175 records, recomputes hashes and lengths, refreshes changed files, and adds report basenames throughout the research root, without an age cutoff. It contains2,501 records,751 changed/new and zero missing at initialization. The inherited qualifications and r111–113 original paths are retained. No generated copy was newly removed: the wider additions deliberately overinclude possible echoes. The exact alias searches and full relevant originals, not path absence, drive the decisions. The qualified index omits some preexisting nonstandard report filenames; it is not exhaustive. Body-level registry screening then found exact resolutions that the report-only screen did not surface. This is a concrete limitation of relying on the report index alone.

Reconnaissance search snippets for reciprocal arctan, Nielsen beta, Wan integrals, oscillatory Turán, and other subjects did not become additional exact screened statements. The three selected statements are precisely the following. Searches were public search/HTTP; no browser was used.

## 1. Gaussian prescribed-split probabilities: campaign duplicate

Swee Hong Chan, Gil Kalai, Bhargav Narayanan, Natalya Ter-Saakov, Moshe White, *Unimodality for Radon partitions of random vectors*, arXiv2507.01353v1 and DCG DOI10.1007/s00454-026-00870-6, published7September2026, Conjecture7.2(2).

For every d>=1,n>=d+2 and independent standard Gaussian X1,...,Xn in R^d, define q_k=P(conv(X1,...,Xk) intersects conv(X{k+1},...,Xn)). The statement asks q_k²>=q_{k-1}q_{k+1} for every2<=k<=n-2. The n=d+2 boundary is already source-proved. This is not just the size distribution of the unique Radon partition.

early-screen.json identifies original r47 SUMMARY/discovery and later r116/r129 reports. The full original r47 discovery was read. Cached actual journal text and arXiv PDF were copied and read; Section7.2 retains the question. r47's full proposed angle expansion has an exact failed sufficient step: individual intrinsic-volume rows need not be log-concave. The surviving missing step is a uniform inequality for the complete parity-selected Crofton sum, for all n,d,k; source log-concavity of internal-angle rows does not control the log-convex external-angle factors. No new universal mechanism resolves this. No finite tests, no reopening, no new credit. The current journal body was not newly downloaded here; its prior retrieval and exact cached bytes are distinguished from fresh receipts.

## 2. Karp–Sitnik shifted upper-parameter ratio: exact public proof

Primary: D. Karp and S.M. Sitnik, *Log-convexity and log-concavity of hypergeometric-like functions*. Fresh arXiv history lists only0902.3073v1,18February2009. The actual published author-hosted copy is JMAA364(2010)384–394, online24October2009, DOI10.1016/j.jmaa.2009.10.057. Read Theorem4, its proof, (10),(11), and unnumbered conjecture on printedp390. The published statement retains the same scope; it corrects the preprint's sign in its Kummer-transformation discussion. No endpoint wording correction is nominated.

Write M(s;c;x)={}_1F_1(s;c;x) and R=M(b+δ;c;x)M(a;c;x)/(M(a+δ;c;x)M(b;c;x)). For every c,δ>0,0<a<b, R decreases on x>0 with exact image(A,1), A=Γ(a+δ)Γ(b)/(Γ(b+δ)Γ(a)). For every c,δ>0,a<b<c-δ, R increases on x<0 with image(B,1), B=Γ(c-a-δ)Γ(c-b)/(Γ(c-b-δ)Γ(c-a)). Negative a,b are allowed in the second clause.

Read actual companion Karp2009 conference body (same conjecture at(19),(20)); Kalmykov–Karp2013 JMAA406400–418, general theorem proofs and Kummer example; Mehrez–Sitnik2014 RGMIA Article132, Theorem1 proof. The last treats shifted LOWER parameters, so its title alone does not exclude the upper-parameter claim. The general gamma-ratio coefficient results likewise do not by themselves provide argument monotonicity.

The cached public trureturing KummerRatio Result, Comparison, Series, Transform, BetaIntegral, BetaAsymptotics, Asymptotics and exact Problems body were then read. They cover literally both clauses above. These are actual explanatory proof bodies, not merely status badges or paths. The public proof's universal mechanism is as follows.

The defining entire positive-coefficient series gives y_s=M(s;c;x)>0 on x>=0 and xy_s''+(c-x)y_s'-sy_s=0. Put h_s=y_s'/y_s and μ_uv=x^c exp(-x)y_u y_v. Direct differentiation yields

    [μ_uv(h_v-h_u)]'=(v-u)μ_uv/x.

For v>u>0, the right side is positive and locally integrable at zero because c>0. The left primitive has limit0 there since h and y extend continuously. Thus h_v>h_u on x>0. For w_s=h_{s+δ}-h_s>0 and S_s=h_{s+δ}+h_s, the Riccati equations give w_s'=δ/x+(1-c/x-S_s)w_s. Consequently

    [μ_{b,b+δ}(w_b-w_a)]'=μ_{b,b+δ}(S_a-S_b)w_a<0.

Again the primitive starts at0; hence w_b<w_a and R'/R=w_b-w_a<0 for every admissible parameter, not a finite sample. This is the same strongest tractable route considered in this lane and is already public.

The public endpoint bridge also covers all upper parameters, not just s<c. For0<s<c the beta integral gives exp(-x)x^{c-s}M(s;c;x)->Γ(c)/Γ(s). The boundary integral becomes integral_0^x exp(-u)u^{c-s-1}(1-u/x)^{s-1}du. On u<=x/2 dominated convergence applies; on the other half exponential decay beats the endpoint beta singularity, so the limit is Γ(c-s). For arbitrary s,c>0 choose an integer m with c+m>s. Repeatedly use the coefficientwise contiguous identity

    M(s;c;x)=M(s;c+1;x)+s*x/[c(c+1)] M(s+1;c+2;x).

Both right terms have larger lower-minus-upper gap, so finite induction extends the normalized limit. The first normalized term is multiplied by1/x; the second has coefficient s/[c(c+1)], giving Γ(c)/Γ(s). The four normalized factors cancel the x and exponential powers, producing A. At zero all M equal1. Continuity, strict decrease and the intermediate value theorem give exactly(A,1). Kummer reflection gives R(a,b,c,δ,x)=R(c-b-δ,c-a-δ,c,δ,-x). Its new upper parameters are positive even when a or b was negative. This yields the entire negative-ray clause and B.

Retirement is for an actual identical public resolution, not a claim that a short proof is intrinsically routine. No fresh PROOF.md or candidate is justified.

## 3. Nikolov snake-polynomial positivity: exact public refutation

Primary latest arXiv pages list only Kryvonos(ed.)2312.07754v1,12December2023, and Manskova2504.04845v1,7April2025. Both fresh PDFs were read: original snake section printedpp6–8 and UP24§7 printedpp12–13. Conjecture7.1: for every continuous even convex μ>=0 on[-1,1], every associated degree-n snake polynomial has nonnegative first-kind Chebyshev coefficients. Snake means degree<=n, global |P|<=μ, and n+1 ordered alternating contacts. This is a substantive universal claim, not its broader open class-finding Problem7.1 or the separate Markov-extremality folklore question.

Closest Nikolov–Shadrin2012 published proceedings body and1210.7795v1 (later2014 proceedings), actual Theorem1.3/Corollary1.4/Theorem1.5 and proof comparisons, were read early. They use positive expansion as a sufficient hypothesis. That hypothesis is not proved by convexity there.

The cached public SnakeChebyshevExpansionRefutation and exact Problems body explicitly repeat both primary versions and refute this precise assertion. Independently checked their full certificate:

    μ(x)=max(1,(4860|x|-1078)/137),
    P(x)=(38656x^6-41568x^4+6831x²-137)/137.

The maximum of two even continuous convex functions is even, continuous and convex, and μ>=1. On0<=x<=1/4, μ=1 and

    137(1-P)=(1-16x²)(2416x^4-2447x²+274),
    137(1+P)=x²(38656x^4-41568x²+6831).

The two inner factors are bounded below by274-2447/16>0 and6831-41568/16>0 respectively. On1/4<=x<=1 put L=(4860x-1078)/137=μ. Then

    137(L-P)=(1-x)(4x-1)(9664x^4+12080x³+2292x²-155x+941),
    137(L+P)=(4x-3)²(2416x^4+3624x³+1479x²+180x-135).

The first quartic is>=941-155>0. The second equals137/2+(x-1/4)(2416x³+4228x²+2536x+814)>0. Thus |P|<=μ over the entire real interval; evenness handles negative x. The seven contacts1,3/4,1/4,0,-1/4,-3/4,-1 have alternating values3782/137,-2567/137,1,-1,1,-2567/137,3782/137. Finally

    P=-(459/274)T0+(1503/274)T2+(2052/137)T4+(1208/137)T6.

The triangular leading degrees of the Chebyshev basis imply uniqueness. Its negative constant coefficient prevents a nonnegative expansion. Reversing orientation makes the leading coefficient negative instead. This is a full real-domain counterexample already public, not numerical diagnostics or a new theorem here. checks.py checks all five polynomial identities, the contact values and the basis expansion using exact fractions. The written lower bounds provide the universal interval bridge.

## Chronology, access and objections

Both public resolutions are present in a cached clone at f8ffe9ed02e01601ed0b43a400ebc1c09cdc6ada. The existing clone log predates this lane; cached-copy-provenance.json records its receipt and each exact content/Git-blob hash. Matching old registry-tree blob IDs authenticate the matching resolution objects. This is sufficient to disqualify a new discovery now. Exact first introduction commits and earliest author-priority dates were not reconstructed. No claim of current HEAD equivalence is made, and no later independent counterpart is falsely called older than our work: these cached bodies were already locally available before this research began.

No GitHub API/raw/codeload/diff, ScienceDirect, Google challenge, IEEE or OpenReview body request was attempted. Search results incidentally returned publisher metadata, which was not used as proof-body access. All fresh source downloads succeeded with recorded status200; denied historical access and capped missing merge trees remain PARKED. Scientific claims do not rely on exhaustive current-registry absence. The decision is positive identification of exact cached prior bodies plus actual source comparison; completeness of the global registry is unnecessary for these exclusions and remains unproved.

Strongest objection to any nomination: exact full public counterparts. Strongest unresolved mathematics here is the old Gaussian parity-sum inequality; it was not reopened. No new target survived the permitted three-statement screen, so further numerical or formal work would be rediscovery. Root owns review/investment/acceptance. Credit0.
