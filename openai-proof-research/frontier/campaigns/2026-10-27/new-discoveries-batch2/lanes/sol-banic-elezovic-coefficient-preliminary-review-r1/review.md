# Preliminary adversarial review — Banić–Elezović coefficient

Recommendation: **EXCLUDE from substantive discovery credit**, while preserving the ordinary proof as a mathematically successful source-method completion. Root alone adjudicates. No acceptance, count, shared file, Git, public posting, MathDB edit, Lean work, manuscript or build was performed. Counts remain **9 additional / 39 total / next 40**.

|Gate|Verdict|
|---|---|
|SOURCE|PASS for the exact v1 question and applicable analytic proof bodies|
|MATH|PASS for the source-dependent ordinary proof, including all three residues|
|SUBSTANTIVE|FAIL: the remaining computation is a finite evaluation explicitly prepared by the source's proved method|
|NOVELTY|Bounded investigation only; no located duplicate resolution, no worldwide or current-registry clearance|
|Formal feasibility|Not certified; feasible in principle with substantial analytic infrastructure; do not invest for campaign credit on this review|

This exclusion does **not** claim that the paper already prints a proof of Conjecture 7.7, or that an earlier publication resolving it was found. The distinction is between an unevaluated coefficient and a missing analytic mechanism. Here the former remains; the latter does not. Proof length is not the criterion.

## Scientific identity and primary-body coverage

Candidate reviewed: `sol-wide-analysis-geometry-mechanisms-r261/PROOF.md`, SHA256 `173f6be1a7c1522a45b8bf856c4cc5b23149ce97577990ed5d70f99ac783d506`. The review uses its frozen copy, not the shorter root triage note. Root's status snapshot confirms no accepted proof; root arithmetic is not imported as verification.

Primary: N. Banić and N. Elezović, *Discrete total variation under the multinomial, Part 2: variance under the uniform null*, [arXiv:2610.17046v1](https://arxiv.org/abs/2610.17046v1), submitted **2026-10-12 16:17:43 UTC**. Frozen PDF SHA256 `25185bd9ff2f8602b5175b98d825f692fd3403bd7ad62ef116385e862b0c04a2`; text SHA256 `f532a98fa09530b44608a679f0b6113fbc3e0a6f1406a5339e9761f451d99b79`. A guarded fresh retrieval of the explicit v1 PDF on 2026-10-30 returned the same PDF hash. Independent guarded `pdftotext -layout` extraction exactly reproduces the frozen text. Typography warning retained in `extraction.json`.

Actual bodies read, with printed pages and frozen text line intervals:

* Lemma 4.4, pp20–22, lines1146–1248: full statement and proof of the periodic kernel and finite-support tensor Abel identity; Eq(6.6)–(6.7), pp41–42, lines2460–2530: characteristic function, all maxima and exact twisted phases.
* Lemma 6.6, pp43–44, lines2554–2610: complete primitive/distributional proof, no hidden delta term; subsequent origin partition/split, lines2611–2634.
* Lemma 6.7, pp44–45, lines2635–2678: complete support-uniform tensor continuity proof, including the one-dimensional subtraction convention.
* Lemma 6.8, pp45–47, lines2679–2810: complete analytic-log proof, inner/outer central windows, complex tube and Cauchy derivative bounds. No abstract-only invocation of Edgeworth theory.
* Lemma 6.10 proof, pp48–49, lines2856–2934: scaling factor, smooth growing cutoff, tail removal, simultaneous parity; Lemma 6.11 and complete Lemma 6.12 proof, pp49–50, lines2935–3035: finite-part Gaussian evaluation and the mixed one-variable estimate with integrable majorants. Twisted-amplitude computation through pp50–51 was also inspected.
* Lemma 7.3, pp55–57, lines3302–3433: complete proof, including s=5 remainder, all origin pieces, twisted saddles, off-saddle derivatives and residue average. Definition 7.4/Eq(7.3), p57, lines3434–3454; literal Conjecture 7.7 and its equivalent residue constants, p60, lines3607–3633.

These are applicable proof bodies, not just theorem labels. The argument below reconstructs the full bridge needed for exclusion without appealing to unread Estrada–Kanwal/Gel'fand–Shilov books or to a generic Gaussian-moment citation. The paper supplies and proves the finite-part identities used here.

Exact target: for every integer ell≥0, let `(X1,X2,X3) ~ Mult(ell;1/3,1/3,1/3)` and `h(ell)=E|X2-X1||X3-X2|`. For each **fixed** r∈{0,1,2}, the source proves, along ell→∞ with ell≡r mod3,

`h(ell)=c_L ell+a_*+b_r/ell+O(ell^-2)`,

where `c_L=2sqrt(3)/(3pi)+1/9`, `a_*=-2sqrt(3)/(9pi)`. The implied constants need not be uniform in an unrelated n. Definition 7.4 defines `a_triangle=1/32+(pi/9) sum_r b_r`. Conjecture 7.7 asserts `a_triangle=1/32-4sqrt(3)/243`, equivalently `d0=-4sqrt(3)/(81pi)`, `b0=32sqrt(3)/(81pi)` and `b1=b2=-22sqrt(3)/(81pi)`. This review covers that complete literal constant question. Fixed-n variance consequences and varying-n limits are not additional results.

## Full source-method bridge and error audit

Lemma 4.4 applies because each ell law has finite integer support: there is no probabilistic limit interchange in obtaining `(2pi)^-2 <S tensor S,Phi^ell>`. Here `Phi=(exp(-ix)+exp(i(x-y))+exp(iy))/3`. The torus finite part is the tensor Abel limit, **not** an unregularized improper integral. Lemma 6.6 proves locally

`S(x)=-2 fp(x^-2)-1/6-x^2/120+O(x^4)`.

The quadratic coefficient follows by differentiating the same smooth logarithmic primitive (or the Laurent series); there is no new normalization choice. The one-dimensional convention is `fp(x^-2)=-(pv(x^-1))'`, with action on f equal to the integral of `(f-f(0)-xf'(0))/x²` over |x|≤1, plus the integral of f/x² over |x|>1, minus 2f(0). It is homogeneous and creates no delta term. Multiplication by x gives pv(x^-1), and by x² gives 1. Hence the candidate's Laurent-polynomial moment manipulations preserve the source convention.

Use the smooth symmetric torus partition of the source. Under x=u/sqrt(ell), y=v/sqrt(ell), the pure singular, mixed, and smooth pieces have outside factors ell, 1, and ell^-1. Set `q=u^T C u`, `C=[[2/3,-1/3],[-1/3,2/3]]`; eigenvalues are 1/3 and 1 and `G=exp(-q/2)=exp(-(u²-uv+v²)/3)`. Choose a fixed 0<epsilon<1/2. In the central window |u|≤ell^(1/2-epsilon), insert the source's smooth window `psi(u/ell^(1/2-epsilon))` along with `chi0(u/sqrt(ell))`. Their derivatives are bounded uniformly, so Lemma 6.7 applies with uniform constants. Outside that window but within the origin patch, the exact characteristic function and its derivatives are bounded by polynomial factors times `exp(-c ell^(1-2epsilon))`; cutoff changes cannot alter algebraic coefficients.

Lemma 7.3 explicitly runs the complete Lemma 6.8 argument with s=5. For every derivative with 0≤a1,a2≤2, the omitted remainder after P5 is bounded by `C ell^-3 (1+|u|^M) exp(-q/8)`. This gives O(ell^-2) after the pure-singular outside factor ell. The Gaussian majorant remains bounded under all derivatives needed in Lemma 6.7. The mixed case uses the one-variable estimate from Lemma 6.12 followed by integration of the Gaussian majorant in the other variable; a supremum bound alone would not suffice there.

For `log Phi(tu,tv)=sum t^k Bk`, the required even central terms are `P2=B4+B3²/2` and `P4=B6+B3 B5+B4²/2+B3² B4/2+B3^4/24`. The unretained P1,P3,P5 terms vanish under **simultaneous** (u,v)→(-u,-v). Neither G nor the general polynomials need be even separately in u and v. The candidate uses the correct simultaneous parity; loose individual-even wording in the source is not needed. Smooth kernel Taylor remainders and their derivatives have uniform polynomial Gaussian majorants on the window. In mixed pieces, retaining P2 and the kernel quadratic term suffices at ell^-1; the ell^-3/2 terms vanish by this same parity. Remaining even terms start at ell^-2. In the smooth×smooth piece the outside factor ell^-1 leaves only s(0)² at the desired order, with the first odd term vanishing. All Gaussian-polynomial tails can be extended to R² using Lemma 6.7 or its mixed analogue.

Consequently the entire origin ell^-1 coefficient is the following **four** terms, with `I(F)=(2pi)^-2 <F,G>`:

`I(4P4/(u²v²)) + I((u^-2+v^-2)P2/3) + I((v²/u²+u²/v²)/60) + I(1/36)`.

This derivation includes the kernel curvature and smooth×smooth terms. Omitting either gives a wrong value. Off the three maxima, derivatives of Phi^ell through order (2,2) cost at most ell^4 and an exponential factor, hence contribute O(ell^-2) (indeed exponentially small). At Q1=(2pi/3,-2pi/3) and Q2=-Q1 the amplitude is smooth with value 4/9. The exact identities `Phi(Q1+eta)=omega_bar Phi(eta)` and `Phi(Q2+eta)=omega Phi(eta)` and the Gaussian integral `2pi sqrt(3)` give each leading amplitude `tau1=2sqrt(3)/(9pi)` times its phase divided by ell; smooth-amplitude Taylor terms of first odd degree integrate to zero, and the remainder is O(ell^-2). Thus

`b_r=d0+4sqrt(3)/(9pi) cos(2pi r/3)`.

Their average is d0 exactly. No fourth saddle, surviving half-integer order, residue-dependent origin term, sharp-cutoff boundary term, or unstated n-limit is left to settle.

## Independent finite evaluation

`check.py` was written for this review and imports **no candidate script or computed result**. It forms the degree-six exponential Taylor polynomial directly from the three increments (-u,u-v,v), takes `log(1+z)=z-z²/2+z³/3` (z starts at degree2), and constructs P2/P4. Expanded B2…B6, P2/P4 and every Laurent-monomial contribution are recorded in `independent-check.json`. All B3…B6 agree with the candidate's displayed coefficients, including the signs of the imaginary odd terms.

For completeness an independent moment recurrence replaces importing the candidate's finite-sum rule. Normalize all moments by sqrt(3)/pi, and write them as T(p,q). Completing the square and integrating the nonsingular variable gives `T(0,k)=J_k/4`, where `J_-2=-1`, `J_0=2`, `J_k=2(k-1)J_(k-2)` for even k≥2 and J_k=0 for odd k≥-1. The negative base follows directly from fp integration by parts: `fp integral exp(-v²/4)/v² dv=-sqrt(pi)`, already proved in source Lemma 6.11. Gaussian integration by parts in u gives

`T(p,q)=(3/2)(p-1)T(p-2,q)+(1/2)T(p-1,q+1)` for p≥2,

and `T(1,q)=T(0,q+1)/2`. Exchange variables if p<0. Every monomial here has p,q≥-2 and at least one exponent nonnegative; hence this recursion terminates at the stated bases and never assumes an undefined double negative base. The inner polynomial Gaussian integral is Schwartz in the remaining variable, justifying the subsequent finite-part pairing. This also derives the candidate's completed-square finite-sum formula by expanding u=(u-v/2)+v/2. No novel distributional identity is being assumed.

The four normalized values are respectively `-11/405`, `-1/36`, `-1/120`, `1/72`, whose exact sum is `-4/81`. Thus `d0=-4sqrt(3)/(81pi)`, the three b_r have precisely the values stated above, and `a_triangle=1/32+(pi/3)d0=1/32-4sqrt(3)/243`. This checks the full finite arithmetic rather than only the final rational sum. The checker is an arithmetic audit; the analytic justification is the preceding source-body reconstruction. Finite-ell diagnostics from the candidate are not used as limit proofs and were not needed for this verdict.

## Substance, prior art and chronology

The strongest objection is sustained. Lemma 7.3 already identifies precisely d0 as the origin's next coefficient, explicitly retains P4 and P5 with the necessary weighted remainder, explicitly expands s through its quadratic term, proves absence of half-integer powers, and evaluates/cancels the twisted leading terms. Lemmas 6.11–6.12 already demonstrate the finite-part Gaussian and completed-square mixed evaluation. After these proved inputs the bridge consists entirely of: differentiating analytic functions six times, multiplying the four kernel/central terms, and evaluating finitely many moments by the proved integration-by-parts rules. The reconstruction above completes every such adaptation; I identify **no new analytic obligation** whose solution would justify retaining this candidate as a substantive discovery. This is not an inference from a short proof or an open label. It is a complete source-method subsumption assessment. The source framework, Gaussian moments, covariance consequences, and potential formalization receive no separate credit.

Bounded live primary check at **2026-10-30 16:12–16:13 UTC**: target abstract/history, author search for Elezovic,N, exact series-title search, explicit target-v1 PDF, and Part1 abstract all returned HTTP200. `live-access.json` and `refresh-access.json` preserve URLs, UTC times, byte counts and SHA256s. The target history lists v1 only; the exact-title search returned Part2 and Part1 only. This is an available-route/version check, not proof that unpublished or unindexed companions do not exist. Source references [5]–[7] label Parts3–5 in preparation; Parts3–4 concern general-law expectation/variance and Part5 cyclic variation. I did not invent a public body for them.

Closest available companion actually body-read: [Part1 arXiv:2610.13366](https://arxiv.org/abs/2610.13366), submitted **2026-10-09 10:39:42 UTC**, frozen PDF `78d7b8a8ff30e8d58cad6db5cab4af72d0e216eca371879d4a0abe2a03f6b580`, text `4ea7aa2454d719c08563e6f07fc36c7f6e41606481ff6826c2d8d10170074711`. Its scope statement pp3–4 explicitly confines it to first moments. Lemma5.4 and complete proof pp18–19, Theorem5.5/proof and Corollary5.6 p19, and Remark5.7 were read: they compute per-edge mean coefficients, for fixed n≥3, not the adjacent product or this d0. The source's own mean-import normalization is not an independent discovery. No companion resolution was located in these bodies; no exhaustive all-paper claim is made.

Administrative ledger/context snapshots were parsed in full, not treated as complete from initially truncated terminal output; no Banić/Elezović/17046 match was found in either. The pinned OpenAI registry reference records commit `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` dated 2026-10-08, preceding this target. The catalogue is orientation only, not clearance. Current registry heads cannot be certified: inherited denied GitHub API/raw/codeload/diff/patch routes remain parked, as do ScienceDirect and Google challenge routes. No retry, historical HEAD loop, proxy, TLS-disable or browser bypass was attempted. No global novelty is inferred from metadata, a conjecture label, an absent catalogue hit, or the lack of an accessible registry head. The SUBSTANTIVE failure is sufficient for the recommendation independently of this unresolved novelty gate.

## Formal feasibility, provenance and failures

No Lean endpoint exists in this review. A faithful formalization would need the literal multinomial expectation, tensor distribution/Abel localization or an independently proved discrete alternative, source-compatible asymptotic remainder bounds and the finite coefficient evaluation. Rational polynomial algebra alone cannot certify the limit. Feasible in principle is not formal PASS, and formalizing this source-method completion would not change its credit classification. No manuscript or build was started.

All scientific originals were frozen before scientific reading into read-only hash-named files; originals and copies were checked at freeze and are checked again by the separate final verifier. Cached Part1 sources were added to the bindings before body reading. New live primary bodies were saved read-only before reading. Immutable prior references were reused narrowly; no historical evidence tree was recursively copied. Administrative snapshots are snapshots only and do not demand immutability of the changing shared originals. `bindings.json` gives exact paths and full hashes; `finalmanifest.json` excludes itself and `verification-receipt.json`; a separate guarded verification follows final writes.

Preserved failures/limits: initial broad native file listing and combined ledger/context display were truncated; neither is used as complete evidence. The setup snapshot reused the AGENTS.md basename and overwrote the batch copy with the ancestor; `more.py` corrected this to distinct batch/ancestor snapshots before review. Root status is administrative only. Independent PDF extraction emitted a font mismatch warning, exited0 and exactly matched the frozen extraction. No mathematical discrepancy or cap breach occurred. Guard-reported peaks: independent arithmetic 57,044,992 bytes / 0.56s; first live check 25,243,648 bytes / 0.69s; PDF re-extraction group 35,774,464 bytes / 0.24s. Every helper/retrieval/extraction/hash ran through the specified helper_guard with AS/groupRSS512MiB, CPU210s, wall230s and OPENBLAS_NUM_THREADS=OMP_NUM_THREADS=PYTHONDONTWRITEBYTECODE=1. No cap was raised. Native bounded reads and apply_patch were used as authorized.

Final disposition: preserve a correct uncredited ordinary resolution; **EXCLUDE** from campaign acceptance investment under the substantive standard. Root alone may adopt or overrule this recommendation. Counts remain 9/39/40.
