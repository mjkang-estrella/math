# Independent adversarial review r2

Review date: 2026-10-29 UTC. SOLO, no children. This is an independent recommendation, not acceptance. All writes are in this lane. No git, browser, account, contact, post, upload, shared edit, Lean invocation, or reading of the changing literal-ODE worker occurred. Frozen ledger: **7 additional / 37 total**; no count change.

## Recommendation and gates

**EXCLUDE from discovery credit as a routine classical comparison corollary.** The ordinary theorem is sound and answers the full surviving published assertion. This exclusion is a substantive campaign-standard judgment based on a completed reduction, not a claim that an identical statement has been found in print, not an inference from proof length, and not a novelty PASS inherited from another lane.

| Gate | Independent result |
| --- | --- |
| Exact published target | Cleared at ordinary source level: all real u≥v>−1, 0<a≤b, all x>0; monotone/constant allowed |
| Ordinary mathematics | Complete bridge below; no infinity asymptotics or missing singular-endpoint condition |
| Classical subsumption / substance | EXCLUDE: full reduction to published Wronskian comparison, first Bessel coefficients, and MVT; no substantive residual estimate or mechanism identified |
| Exact earlier full-ratio printed theorem | Not established in the bodies screened; do not label this a printed duplicate |
| Current registry / literature priority | HOLD: current complete heads/deltas not established; bounded negative searches do not establish priority |
| Literal formal endpoint | HOLD / not reviewed as complete: the frozen generic component supplies only standard comparison; literal Bessel hypotheses remain outside that component |
| Acceptance / credit | None; root alone decides |

The root r1 provisional INVEST judgment is understood but not adopted. Its counts were 6/36 at 16:01; this review's frozen ledger is 7/37. Neither the newer generic formal component nor formalization effort increases substantive depth.

## Evidence freeze and provenance

Before substantive source reading I copied 55 supplied files to `frozen/`, with original-before/copy/original-after SHA256 equality recorded in `input-freeze.json`. This includes ancestor and batch AGENTS, ledger and prior-campaign context, upstream pin/catalogue, r57 discovery and primary sources, r1 review and primary comparison bodies, root adjudication, the stable generic SUMMARY and three Lean modules, acceptance-prior limits, and the actual saved Lean D5 tree. The AGENTS and the r1 review were initially inspected to establish instructions and locate evidence before this bulk freeze; those initial reads are disclosed rather than called pre-read frozen. Subsequent reasoning used own copies. No changing ODE files were inspected. `input-after.json` rechecks the originals at handback; public-download and local-artifact hashes are in `provenance.json`. Changed originals, if any, do not change the reviewed frozen version.

Fresh public HTTP requests and response UTC, URL, response headers, byte counts, and hashes are in `http.jsonl`; downloaded bodies and extracted texts are under `public/`. All requests succeeded. Fresh publisher PDF and Krüger–Teschl PDF match the earlier frozen bodies respectively:

- KVZ: `1ba19be497b661f25b6572b0c35afb938974ba8807965ec38be7693691db8115`.
- Krüger–Teschl: `944b46aa9965bdbbef06c2502ec164900e2797c44b2645a7227fe85312e4a069`.

Search responses are retained in `search2.json`, `search3.json`; the initial four searches were tool-observed but their full response was not separately saved. Search terms included DOI, exact title, Karp/Vishnyakova/Zhang plus Bessel conjecture/proof, modified Bessel ratio unimodality, and Wronskian comparison. Search is discovery evidence only. No numerical universal-proof claim is made, and no unnecessary numerical checker was run.

## Exact published scope and chronology

Read actual final PDF §§2 and 4, especially PDF pp.6,17–18, [KVZ, Results Math. 80:112 (2025)](https://doi.org/10.1007/s00025-025-02431-4). The final §4 paragraph leaves the Bessel-ratio assertion for all real orders u≥v>−1, inheriting positive ordered scales 0<a≤b. The ratio variable is positive real x. The source's unimodality convention admits monotone and constant functions and either orientation of a turn. Our conclusion is stronger: any genuine turn is a peak.

The preceding proof is only for u−v=2ℓ with positive integer ℓ (and mentions equal order separately); Theorem 4.3 is a Q-function integral-transform consequence with that even-integer restriction. It is not the full arbitrary-real-order theorem. Discarding x^(u−v) and applying a common power-series quotient rule would not prove the target: multiplication by an increasing power does not preserve unimodality in general.

Fresh [arXiv history](https://arxiv.org/abs/2408.01755) gives v1 2024-08-03 11:37:28 UTC and v2 2025-03-01 11:59:59 UTC; v2 is still the listed revision. Publisher dates: received 2024-09-10, accepted 2025-04-26, version of record 2025-05-20. The earlier author manuscript's separate positive-order log-concavity clause is absent from the published ending. Do not import that clause into this target.

The frozen public Omega path history records `c27ba49982568b4465a7808f7a503faf0b61976b`, 2026-10-25 08:06:22 UTC, documenting the log-concavity refutation. This precedes the local October29 Bessel work, but proves a different assertion. At the user-supplied later observed head `6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3`, I independently retrieved/read the immutable [problem body](https://raw.githubusercontent.com/the-omega-institute/trureturing/6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3/Problems/karp-vishnyakova-zhang-2025-bessel-ratio-log-concavity.md) and [actual Lean result](https://raw.githubusercontent.com/the-omega-institute/trureturing/6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3/D5/S3/Analytic/BesselRatioLogConcavity/Result.lean). The encoded claim is positive-order log-concavity; result negates it. The witness uses equal order 1/10 and scales 1,2. The problem explicitly excludes unimodality from its claim. No novelty or credit for that already public refutation is available here. This is targeted immutable source reading, not an alternate endpoint for discovering a blocked API head.

## Full classical bridge, independently closed

First read the actual Krüger–Teschl body, §§2–3, equations (2.2)–(2.5), Picone identity (3.2), and Theorem 3.1: *Relative oscillation theory for Sturm–Liouville operators extended*, JFA 254 (2008),1702–1720, DOI [10.1016/j.jfa.2007.10.007](https://doi.org/10.1016/j.jfa.2007.10.007), [author PDF](https://www.mat.univie.ac.at/~gerald/ftp/articles/RelOsc2.pdf). This theorem explicitly includes zeros of Wronskians. I do not substitute a textbook theorem about zeros of solutions alone. Its references to singular-endpoint extensions are not needed in this application.

Let f(x)=I_u(ax), g(x)=I_v(bx), δ=u−v≥0, s=u+v, A=u²−v²=δs, B=b²−a²≥0. For ν>−1, Γ(k+ν+1)>0 for every k≥0. Thus the standard series gives f,g>0 on (0,∞). Factoring x^ν leaves an entire series in x² with locally uniformly convergent differentiated series. Hence f,g are C² on every positive compact interval, even for negative noninteger orders. Direct series substitution gives

    (xf')'=(a²x+u²/x)f,    (xg')'=(b²x+v²/x)g.

In the published notation take p0=p1=x, r=1, q0=b²x+v²/x, q1=a²x+u²/x, u0=g, u1=f, λ0=λ1=0. Then W(g,f)=x(gf'−g'f) equals W=x(f'g−fg'). All hypotheses p,r>0 and 1/p,qj,r locally integrable hold on (0,∞); solution/flux regularity holds on every interior compact. Equation (2.5) gives exactly

    W'=(A/x−Bx)fg,          (f/g)'=W/(xg²).

No self-adjoint boundary condition, L² behavior, regular extension through zero, or signs of f',g' are premises. There are no solution zeros since f,g>0. On any interval where q0−q1>0, Theorem 3.1 says two zeros of W would force a zero of f. Consequently W has at most one zero on that interval. Strictness is satisfied throughout each interval where we use this argument, not merely assumed at an endpoint.

Here is all target-specific endpoint work. Put C=(a/2)^u(b/2)^v/[Γ(u+1)Γ(v+1)]>0. With α=a²/[4(u+1)], β=b²/[4(v+1)], write f=c_u x^u(1+αx²+O(x⁴)) and g=c_v x^v(1+βx²+O(x⁴)). These are convergent factored series, so differentiated remainders have the required orders. Therefore

    δ>0: W/(Cx^s) → δ,
    δ=0: W/(Cx^(2v+2)) → (a²−b²)/(2(v+1)).

For δ>0 this proves W>0 sufficiently near zero irrespective of s. In particular s<0 permits W→+∞: imposing W(0)=0 would be false. For δ=0, v>−1 implies 2v+2>0, so W→0. These observations close the singular-endpoint issue without applying the comparison theorem at the endpoint.

The complete sign cases are:

1. δ=0. A=0 and W'=−Bxfg. If B>0, W is strictly decreasing; for 0<y<x, W(x)<W(y), and the right zero limit gives W(x)<0 (for strictness compare x to x/2 first). If B=0, f=g and ratio=1.
2. δ>0, A≤0. If (A,B)≠(0,0), W'<0 everywhere. Initial positivity implies either positivity everywhere or exactly one positive-to-negative crossing. Equivalently Theorem 3.1 excludes two zeros because q0−q1=Bx−A/x>0. If A=B=0, W is constant and positive, from the normalized endpoint and s=0.
3. δ>0, A>0, B=0. W'>0 everywhere; initial positivity gives positivity everywhere.
4. δ>0, A>0, B>0. Set t=√(A/B). W'>0 on (0,t), W'<0 on (t,∞). Its initial sign implies W>0 on (0,t], so a zero at t or before t is impossible. On (t,∞), q0−q1>0 and Theorem 3.1 excludes two W zeros; the strict decrease also proves any zero crosses from positive to negative.

For completeness, the crossing alternative requires no infinity limit: if W is not positive everywhere, choose a nonpositive finite value and a smaller positive value. Continuity/IVT supplies a zero; the preceding strict monotonicity on its region gives the signs on both sides. A zero cannot be an isolated flat contact. Then xg²>0, the derivative identity and MVT imply strict increase throughout, strict decrease throughout, or increase followed by decrease. All real allowed orders and equal-scale/order cases are exhausted. A constant ratio forces W≡0, hence A=B=0; δ>0 was already shown to have positive W, so constancy occurs exactly for u=v,a=b.

This is a **complete subsumption bridge as a routine application of classical comparison plus standard defining coefficients**. It is not a claim that Theorem 3.1 alone, with no endpoint analysis or sign-region split, states the full Bessel result. Direct monotonicity from (2.5) already suffices; invoking Theorem 3.1 is an independently checked published comparison route, not additional new machinery. No substantive analytic premise is left unproved in the ordinary bridge.

## Strongest objections, contrary case, and falsifiers

The strongest case for INVEST is substantial in scope: the full published four-parameter continuous-order assertion survives its own even-difference proof; negative orders destroy the simplistic W(0)=0 shortcut; a one-turn W' can allow two W zeros; and the full result was still left as a belief in the final article. The root's earlier provisional judgment expressly treated the endpoint/sign bridge as a minimal contribution. Prior accepted ledger entries also caution against a blanket rule that elementary proofs cannot count. These are reasons to review this proof carefully, not reasons to presume novelty or triviality.

Nevertheless my independent standard judgment is EXCLUDE. Once the positive standard solution is substituted into the published Lagrange identity, the potential difference is visibly A/x−Bx. The only additional local information is its defining leading coefficient (and next coefficient for equal orders); no nontrivial estimate, normalization theorem, zero-location result, global asymptotic, or creative parameter restriction is needed. The region split is elementary order analysis of A−Bx². The divergent endpoint is accommodated simply by normalizing by a positive power; it introduces no new analytic construction. Thus the complete bridge is routine for positive second-order equations, rather than an instance where merely classical ingredients happen to support a substantive new mechanism. This is a depth judgment with the mathematical bridge exposed for root to disagree with. A printed exact endpoint is not required to apply the campaign's routine-corollary exclusion.

Concrete falsifiers of overclaims:

- W' changing sign once is insufficient without initial sign: W=1−(x−2)² on (0,4) has two zeros and one derivative sign reversal. This invalidates a shortcut, not the complete proof above.
- Equal scales do not imply increase for all distinct allowed orders: u=−1/4,v=−3/4 gives A<0. The proof correctly leaves a possible peak; it never assumes u²≥v² from u≥v.
- W cannot be assigned zero endpoint data for all allowed orders: any δ>0,s<0 has divergent positive W by the explicit limit above.
- No peak existence is inferred just from a≤b. The proof needs only an at-most-one-turn conclusion.
- The public log-concavity counterexample does not refute unimodality; strict decrease is allowed by the target.

An earlier exact full-ratio theorem would strengthen exclusion on priority grounds. Conversely, overturning the present substantive judgment requires identifying genuinely nonroutine work in the displayed complete bridge or showing that a purported elementary step fails. Merely failing to locate an exact printed statement, or completing the literal Lean implementation, would not overturn it.

## Citing, follow-up and full-prior screening

I read theorem bodies, not only snippets, for these nearest candidates. This is a bounded screen, not a full citing-corpus or specialist database audit.

- Frozen Nanthanasub–Novaprateep–Wichailukkana, Advances in Difference Equations 2019:379, actual §2 and Theorem4: log-concavity/convexity of t^μ Iν(t), ν>−1/2 and explicit μ regimes, and related products. Individual-factor log-curvature does not imply curvature or unimodality of an arbitrary quotient; this does not supply the full target. Source URL is preserved in r57's frozen provenance.
- Frozen Salazar, [arXiv:2607.05538v1](https://arxiv.org/pdf/2607.05538v1), actual defining ratios and §§3–6: adjacent-order power-Bernstein result for ν>−1, individual-I concavity/Riccati bounds, K-quotient classification, and transfer counterexamples. Arbitrary two orders and two scales are not the hypotheses of those results; no full subsumer was found there.
- Fresh Derbazi, [arXiv:2502.13136v1](https://arxiv.org/pdf/2502.13136v1), actual §4.2 Theorem4.6: quotient-of-transforms modality under SR kernels, regular sequences and coefficient-quotient modality. It still requires a common-kernel representation and appropriate input modality. The arbitrary x^δ factor in the Bessel quotient is not removed by that statement. Generic preservation machinery is not credited and is not treated as a complete printed subsumer without those premises.
- Fresh Qi, [arXiv:1302.6731v1](https://arxiv.org/pdf/1302.6731v1), actual Theorem1.2 and displayed Fβ,Gβ: fixed-order I1/I2 expressions against elementary/trigamma-related terms, not the four-parameter I/I quotient. Its unimodality vocabulary alone is not a match.
- Fresh Golrezaei–Hajiaghayi–Shin, [arXiv:2604.04844v1](https://arxiv.org/pdf/2604.04844v1), actual Theorem3 and §7 Lemmas19–20 plus citation context: Bernstein-basis/variation-diminishing control of contest gradient sequences. It cites KVZ for total positivity; it does not state the Bessel-ratio theorem. This independently checks the citer mentioned in the Omega body, without promoting that body's one-citer search to completeness.
- Fresh Salazar [arXiv:2606.31647v1](https://arxiv.org/pdf/2606.31647v1), actual motivation, transport theorem and applications: order-moment/Hankel transport for Mills, Tricomi and Coulomb functions. The web-search abstract had a different q-gamma emphasis; I rely on the downloaded v1 body, not that snippet. No full Bessel-ratio subsumption follows from the actual checked applications.
- Current author publications list [Karp](https://dmkrp.wordpress.com/publications/) and exact-title/DOI searches locate the original work and neighboring 2026 publications. No matching full-ratio follow-up located in this bounded scope. I did not body-read every author publication or all worldwide citations.

None of these bounded negatives establishes priority. The decisive affirmative classical bridge is the explicitly checked 2008 comparison and ordinary derivation above, not an absence search.

## Current registry limits, corrected tree scopes

The inherited shared GitHub API exhaustion at 15:49 and the frozen r1 15:55:55 UTC HTTP403 are respected. No fresh API head request, blind retry, credential switch, alternate head-discovery endpoint, or limit bypass was attempted. The supplied logs do not establish an expired reset for this reviewer; I do not invent one. Targeted normal raw reads above retrieve two named public immutable bodies only, and do not claim to refresh the branch head. **Current complete public-registry clearance remains HOLD.**

Latest observed Omega head is the supplied `6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3`, not independently rediscovered current HEAD. Earlier r57 observation was `3b4135a35caa0ae817cf5eca51d605b098027fd2` (commit UTC 15:32:31 on October29). My own `scope-check.json` verifies:

- r57 `omega-D5.json`: tree `56e3ee94625deab6013ba2dca95c587ba1779496`, 23,236 entries, truncated=false, SHA256 `a279d944837dc2ba420fb86751e9e8449fd6b1c9505adf752e6903f91a58b0b4`; **Blueprint/D5 markdown and scribe**, not actual Lean D5.
- final-review `live/omega-D5.json`: tree `ff3d4cc93223ff3ad37f11018a74d420c0d46f40`, 12,552 entries, truncated=false, SHA256 `04915d127e60d7d39378be1f2bc6bd548c74842f940bd810aadee3661b04da7b`; actual Lean D5.

The BesselRatioLogConcavity entry is present in both different-format trees. I make no unchanged-content or complete-head-delta claim by matching stems. The precise polyomino acceptance-prior limits are frozen and read; their explicitly bounded acceptance is neither Bessel clearance nor permission to erase a head gap.

Other r57 registry observations remain historical: Omega main `d7af67136d4478875778ac6e75eb5fbb8b3693a5`, OpenAI `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`, AIM `8729eab98bafe409b66c5e39253bf56569a62327`, count-ex-machina `dbf673741a54c7dc9d88a6aec0e8148a538f4a3a`. I did not independently refresh their heads or body-audit all their named trees. The ancestor OpenAI pin `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` is an upstream truth source, not a current-priority certificate. The prior thirty's Bessel–Fourier positivity refutation is a different family/claim; no second credit or reused witness is proposed here.

## Formal component and resources

Read frozen SUMMARY and source-facing declarations in Crossing/Transfer/Cases. `unimodal_transfer` assumes positive p,D, W'=(A/x−Bx)p, B≥0, either initial positivity or the specified zero-limit branch, and R'=W/D. These are precisely the standard comparison premises just used. The component does not define the literal Bessel/Gamma series or discharge the scaled ODE, positivity, endpoint normalization, or full source-definition connection. Its reported formal PASS is not independently replayed here and is not inherited as a literal endpoint PASS. No credit for this machinery.

Every Python helper ran under the copied guard: address space512MiB, process/group sampled CPU210s, group RSS512MiB, wall230s, BLAS threads1. The 40ms RSS sampling cannot exclude between-sample spikes. Freeze peaked about23.6MB; fetch44.5MB; scope/read49.999MB; extra fetch47.3MB. No helper cap failure or limit increase occurred. The guard logs retain exits and timings; the original freeze output was tool-observed, and the finalizer has its own log. No Lean replay was necessary or attempted.

Final position: ordinary proof complete; exact-priority status HOLD; substantive recommendation EXCLUDE for the fully exhibited routine classical bridge. This review supplies no acceptance or count authorization.
