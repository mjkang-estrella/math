# r54: full p-Seidel maximum remains unresolved (credit 0)

No complete source theorem/refutation, nomination, eligibility PASS, Lean or paper. All writes are in r54. Root owns acceptance; counts observed 6 additional/36 total are unchanged.

## Scope and four primary screens

1. Distance-Laplacian Brouwer analogue: Huang, arXiv:2606.06945v1, actual pp1–3, then current published AIMS Mathematics 11(10) (2026) 33617–33633, DOI10.3934/math.20261314. This public source itself gives K1,3 at r=2 and K1,4 at r=3 as exceptions. The blanket inequality is already refuted. A further search hit claims path refutations, but that hit was NOT relied on as a verified primary proof. Rejected before mathematical investment. The RevUMA current journal landing page was also saved; its full final PDF was not obtained/read.
2. Li–Guo, Filomat39:13(2025)4551–4564, actual publisher PDF. Conj1.1 excludes C_(4k+1) but its disconnected formulation and Conj1.2 have public corrections dated October26, before this lane. Source Conj2.22 is a signless-Laplacian positive-part square inequality; C3 has q=(4,1,1), LHS4 and RHS3. This trivial small-exception issue is ineligible under the user's exclusions and was not nominated. The public correction record and its attached NOTE.md were obtained; the full note was subsequently read and explicitly leaves connected Conj1.1 open. No assertion that its correction resolves the substantive connected Conj1.1.
3. Square energy: Akbari–Kumar–Mohar–Pragada EJC32(3)(2025)#P3.53; publisher PDF saved. Its full connected-graph conjecture min(s+,s-)>=n-1 already has Liu–Tang–Zhang arXiv:2607.18031v1 (July20) Theorem1.2. Actual theorem/definitions read; no attempt to reprove or credit. No full audit of their proof is claimed or needed for exclusion of an existing public proof claim.
4. Selected target: Guterman–Saha, *Extremal problems on the p-Seidel energy of graphs*, arXiv:2606.17828v2, Question5.1, actual PDFp25. Current arXiv abstract/history identify v2 (August24; manuscript dated August25). No later journal version was located in the bounded title/author searches. The v1 abstract overstates some scopes: use the actual v2 body. No fifth primary target was screened.

## Literal selected question and definitions

For every integer n>=2 and every real p>2, characterize all finite simple undirected graphs G on n vertices that maximize

    E_p(S(G)) = sum_(i=1)^n |lambda_i(S(G))|^p,
    S(G)=J-I-2A(G).

Eigenvalues carry algebraic multiplicity. Connectivity and regularity are NOT assumed. Switching S -> DSD (D diagonal +/-1), complementation S -> -S, and vertex permutation preserve every E_p. The natural proposed answer is exactly the switching/complement class of the complete graph, with value (n-1)^p+n-1. This answer is a research conjecture here, not the source's asserted formula. A violating graph would disprove that proposed answer; it would not itself fully answer an open characterization question.

Actual v2 Sections2–4 read selectively: Theorem2.2 imports only E_p>(n-1)^p+n-2 for 0<p<2; Theorem2.8 concerns the *minimum* for p>2 via conference matrices. Section4 Lemma4.3 fixes one eigenvalue -1, and applies for p>=3. Theorems4.9/4.11 impose regularity and n=2r or n=2r+2. They are not an all-graph all-p result. We did not silently transplant their constraints.

Closest actual antecedent body: Akbari–Einollahzadeh–Karkhaneei–Nematollahi arXiv:1901.06692v1, Theorems1–2 and Section2 opening proof, pp2–4. Its main endpoint is the p=1 *minimum*, and its positive determinant-coefficient mechanism gives a strict lower bound for 0<p<2. It does not give the desired maximum p>2. Its proof explicitly uses Cauchy–Binet for minors of S and the log-determinant integral. Haemers2012 original PDF saved. The 2024 short-proof DOI10.1016/j.laa.2024.05.001 was identified but its body was not obtained: prior-art clearance remains incomplete.

## Route A: scalar spectral optimization fails, exactly

Trace and second moment satisfy sum lambda=0, sum lambda²=n(n-1), and |lambda|<=n-1. Even these three constraints do not imply the proposed maximum. At n=5, use the relaxed vector (sqrt10,-sqrt10,0,0,0) and p=21/10. It has energy 20*10^(1/20), whereas the complete graph has 16*4^(1/10)+4. The exact integer inequalities

    1122^20 < 10*1000^20,
    1149^10 > 4*1000^10

imply a strict gap greater than 20*1.122-(16*1.149+4)=7/125. This vector is not claimed graphical. In fact tr(S^4) for a five-vertex Seidel matrix is 100 modulo16: its diagonal-square contribution is80 and twenty off-diagonal odd squares contribute20 modulo16. The relaxed vector has fourth moment200, incompatible with that congruence. Thus this is precisely a method obstruction, not a source counterexample. Source discrete sign structure is essential.

## Route B: determinant comparison changes sign on a genuine graph

For C5, direct multiplication gives S²=5I-J. Hence

    det(I+tS²)=(1+5t)^4,
    det(I+tS(K5)²)=(1+16t)(1+t)^4.

The first minus the second is positive at t=1 and negative at t=100. Exact values are in exact-checks.json. Neither global determinant ordering is available. The failure is structural, not a rounding artefact: C5 is singular, while K5 is nonsingular.

For 1<q<2, the convergent identity

    x^q = c_q integral_0^infty (tx-log(1+tx))*t^(-q-1) dt

has positive c_q (define it by the same integral at x=1). Near zero the integrand is O(t^(1-q)), and at infinity it is O(t^(-q)), so convergence holds including x=0. Substitution proves the identity. Since sum lambda² is fixed, the energy difference is the *negative* weighted integral of the log-determinant difference. Route B therefore needs an integrated comparison that tolerates the observed crossing; pointwise comparison cannot establish it.

## Route C: exact positive-series reduction; termwise comparison also fails

Let 2<p<4, q=p/2, M=(n-1)², T=I-S²/M and T0=I-S(Kn)²/M. The spectral bound ensures 0<=T<=I. Put

    a_k=(-1)^k binom(q,k), k>=2.

All a_k>0 because a2=q(q-1)/2 and a_(k+1)=a_k*(k-q)/(k+1). The generalized binomial expansion gives, for 0<=t<1,

    (1-t)^q = 1-qt+sum_(k>=2) a_k t^k.

As t increases to1, monotone convergence of the positive series gives sum a_k=q-1, so the formula also holds at1 and is absolutely convergent on [0,1]. Apply it to each eigenvalue of T. The constant and linear terms cancel because tr T=tr T0 is fixed. Consequently the proposed energy bound in this interval is EXACTLY equivalent to

    sum_(k>=2) a_k [tr(T^k)-(n-1)*(1-1/M)^k] <= 0.       (* UNPROVED *)

For genuine C5, the bracket is

    delta_k=1+4*(11/16)^k-4*(15/16)^k.

It is negative for k=2 and positive for k=30: 4*15^30<16^30, so the latter is greater than0. Thus universal nonpositive brackets are false. This third route is not merely a restatement of the scalar relaxation: it retains the exact matrix through its normalized-square moments and gives a positive-weighted cancellation target. No uniform inequality for their total was proved. A truncated series is not enough; sum_(k>K) a_k = (-1)^(K+1) binom(q-1,K), from Pascal telescoping, gives a rigorous tail bound n times that expression, but a finite check using it would remain a particular-graph certificate.

## Classical even moments and why interpolation does not close the target

For even p=2m, expand tr S^(2m) as closed walks. Each signed product is at most its unsigned counterpart; therefore E_(2m)(S)<=tr(J-I)^(2m)=(n-1)^(2m)+n-1. This is an elementary classical comparison, not a discovery. For p=4, equality requires every four-cycle sign product positive. If n>=4, this makes all triangle sign products equal: two triangles sharing an edge have product equal to a four-cycle sign, and the graph of triangles connected by shared edges is connected. Switching at one vertex then makes every edge sign equal. Thus the expected switching/complement equality class holds at p=4. n<=3 is immediate. None of this resolves all real p>2. Log-convex interpolation of norms at adjacent even integers only gives a product of the endpoint bounds, generally larger than the required sum (n-1)^p+n-1. A stronger mechanism is still needed.

## Diagnostics and strongest objections

The fixed graph atlas is a small falsifier screen, not a scalable enumeration programme. All1251 graphs of orders2–7 were evaluated at p=2.0001,2.01,2.1,2.5,2.99,3,4,6; no violation of the proposed complete-graph value beyond floating tolerance1e-7. This does NOT certify the maximizers/equality class, all exponents, or higher orders. Exact rational code separately checks RouteA bounds, C5 multiplication and determinant sign changes, and RouteC signs/recurrence for q=21/20. Its 60-term negative partial sum is not a proof of the infinite sum or source question.

Strongest objection: no universal inequality (*) or alternative all-p argument exists in this packet, and even the proposed maximizer characterization remains unproved. Partial classical cases and finite agreement are not eligible. The most direct falsifier is a genuine +/-1 zero-diagonal symmetric matrix with E_p>(n-1)^p+n-1 for some real p>2; to settle the source one would then still need the correct full characterization. A claimed complete proof must also establish all equality cases.

## Current registries and bounded chronology

At15:26UTC all five public heads were refreshed. Omega dev moved from b386687d... to0169726ddb84961c464ea4c20f56324352aafe08; four other heads stayed unchanged. Compare API returned300 files and is NOT complete whole-dev coverage. We therefore separately refreshed complete D5 (12554 entries, truncated=false) and Problems (1551 entries, truncated=false). D5 adds exactly two mathematical blobs: MinimalFlowDilationMixing and CriticalThetaTailPeak; their actual theorem endpoints concern minimal real flows and zeta theta-tail peaks, respectively, not graph-energy extrema. Problems unchanged. No whole-dev semantic absence claimed.

The named Seidel matches were fetched at current immutable head. Actual source-matching claims and supporting proof portions concern p=1 chain-graph minima, single-edge deletion of distance-Seidel matrices, and switching identities. Their hypotheses/endpoints differ from Question5.1; this is a bounded scope comparison, not a proof of global absence. Current OpenAI complete preprints, AIM and Count cached complete trees retain their hashes and had no corresponding filename hit; no assertion that filename screening is semantic clearance. The current public Seidel source still posing a question is also not novelty proof. No novelty PASS or priority claim.

All HTTP requests succeeded200; no403/429/challenge was encountered or bypassed. URL, actual UTC, source-byte count and SHA256 records are in http.jsonl/provenance.json. Search results are bounded, not a MathSciNet/zbMATH or exhaustive citation audit. No browser, account, upload, posting, contact, git operation or child agent.
