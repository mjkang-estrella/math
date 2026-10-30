# Targeted source and prior-body review r2

**Recommendation: exclude r97 from discovery credit as a routine consequence of an earlier public construction. Ordinary mathematics and accepted-manuscript attribution remain PASS. Published-version comparison remains HOLD. Broader historical/registry semantic clearance remains bounded and incomplete. Credit 0; counts unchanged at 8 additional / 38 total.**

This changes the preliminary substantive verdict for a specific reason: the actual proof of Ruankong–Santiwipanont–Sumetkijakan, Theorem 5.4, supplies the missing compatible-triple construction. This is stronger evidence than a new elementary alternative, an open-question label, or a negative search. It does not assert that r97's exact six formulas appeared previously, or that an earlier paper printed this precise Chatterjee conclusion.

## Frozen inputs and scope

Solo review, no children. Read ancestor and batch AGENTS, current NEXT, ledger/counting rules, prior-campaign context, root ADOPTION, full candidate PROOF, full preliminary review, and actual primary passages discussed below. `freeze-before.json` verifies and copies all 59 candidate files and all 98 preliminary files against the two root manifests. `freeze-after.json` rechecks originals and copies. Reviewed proof SHA256: `48b08f770af4241f8b3fc52f00db368590c366da5bd3c844907f1431f993dad4`. No candidate or shared writes, git, Lean, manuscript, browser/preview, contact, accounts, posting or uploads. All writes are in this lane.

Every executed Python helper uses the unchanged improved guard copied byte-for-byte from `sol-edge-irregulator-manuscript-packet-r1/packet/helper_guard.py`: AS and group RSS 512MiB, CPU210, wall230, nominal40ms, BLAS1. PDF text extraction is a child of the guarded fetch helper. No caps raised. Fetches use ordinary public HTTP with no blocked-publisher retry or access bypass. Local cat/rg/sed/diff are bounded reads. Original-byte receipts and hashes are preserved.

The candidate's six directed values and all-K choice are sound as already independently checked. I read their conditional-law derivation and found no new math objection. This review does not repeat finite arithmetic tests or provide a formalization.

## Priority 1: distinct author body obtained, final published body still unavailable

Fresh Giacchini author PDF is byte-identical to the frozen accepted body: SHA256 `53318dbd97dd06354f157c06bfad77ad746ef6bdfe831857bbac5efc6f95a690`. I read its definitions, Theorem2, Lemma5/Theorems6–8, and conclusion. The source's correlation-min distance is **max of directed distances**, whereas its d-prime is min of distances. Theorem2 proves the all-K failure for the latter. The conclusion pp17–18 asks approximate variants for the other three. The accepted-manuscript uniform multiplicative scope remains PASS, without claiming every possible additive/distribution-restricted question solved.

A distinct legitimate route succeeded: [Chierichetti's own publications page](https://www.chierichetti.name/publications) explicitly links [this public author PDF](https://drive.google.com/uc?export=view&id=1EbhRIBo3hoERFLHWUOVwIv4IiJgUDXTX). SHA256 `d3377b166df15c56aeeeff6e3c83641e709e2c99c0fcb1738ce7e9ce15f28a14`, 446956 bytes. It is dated April17,2026 rather than February21,2026. **All extracted text is identical except that title-page date**; `author-comparison.json` records the comparison. Both explicitly say Accepted Manuscript. This closes the ambiguity about that second author-hosted copy; it does not certify VoR equivalence. The post-publication author dates do not replace accepted posting October10,2025 / online November19,2025. Publisher metadata TAS80(2)310–317 is bibliographic evidence only.

The source-linked code repository tree is complete/nontruncated at `b0a0c799d4f732d0e193554cd548e46883580ac4`; README describes experimental code and its PDF files are plots, not a final article body. The Sapienza author catalogue page retrieved successfully but its displayed page does not include this title; the separate ordinary title-search URL returned404 once and was not retried. Title/DOI searches found no distinct lawful full VoR body. Search snippets are not full-body evidence. Publisher403 inherited from previous work was respected: no new publisher request, endpoint variant or bypass. No file-broker/contact route used. **VoR HOLD remains**, candidly; neither author copy is relabeled final.

## Priority 2: decisive older compatible construction

Primary full public body: [Ruankong, Santiwipanont and Sumetkijakan, Shuffles of copulas and a new measure of dependence](https://arxiv.org/pdf/1204.0405), arXiv1204.0405v1, public submission April2,2012 (the PDF footer has a later typesetting date). Journal record: JMAA398(1)(2013)392–402, DOI10.1016/j.jmaa.2012.08.061. This review relies on the **actual public author-preprint proof**, not an unverified assertion of word-for-word journal equivalence. It is an earlier public mathematical antecedent regardless of that equivalence.

I inspected the Sobolev norm definition p5, Theorem2.1, the shuffling/variable interpretation around Corollary4.9 and Theorem4.11, and **the full proof of Theorem5.4 pp22–23**. The latter is the previously missing bridge. For a completely dependent pair `(X,Y)=(U,f(U))`, it constructs measure-preserving a.e. bijections `b_j` of the first variable such that the copulas

    H_j = Copula(b_j(U), f(U))

have Sobolev norm tending to1. More specifically, its successive sorting maps put support in the union of diagonal dyadic squares of side 2^-j. These are maps of the **same U**, not independent pairwise copula choices. The proof states both the product-copula representation and this support construction explicitly.

### Complete all-K bridge, with orientation checked

Use the already public Fuchs–Wang Example2.5 modulo pair with k=2: `X=U`, `Y=2U mod1`. In conditioning-first orientation,

    xi(X,Y)=1, xi(Y,X)=1/4.

Set `A=Y`, `B_j=b_j(X)`, `C=X` on this one probability space. Theorem5.4 gives precisely these re-orderings, with `B_j` uniform and bijective a.e. in `C`. Thus

    d(B_j,C)=d(C,B_j)=0,
    d(C,A)=0, d(A,C)=3/4,
    d(A,B_j) -> 0, d(B_j,A)=0.

For the last line: `Y=f(b_j^-1(B_j))` is still deterministic, hence xi(B_j,Y)=1. Also the Sobolev definition gives

    xi(B_j,Y)+xi(Y,B_j)=6 ||H_j||^2 - 4 -> 2.

Each coefficient is <=1, so xi(Y,B_j)->1. This uses derivative-norm convergence, **not weak continuity of xi**. Alternatively the actual diagonal-square support makes the conditional range of B_j given Y have width <=2^-j, giving d(Y,B_j)<=3*2^-j by the conditional-copy identity. The support property itself is in the old proof; it is not a new selection of a triple here.

Write e_j=d(A,B_j). The source distances then have triangle numerators/denominators

    directed: 3/4 versus e_j;
    max:      3/4 versus e_j;
    average:  3/8 versus e_j/2.

For any K>0 choose j with K e_j<3/4. The SAME triple violates all three multiplicative inequalities. If e_j=0 at some j, it already violates them; no division by zero is needed. This proves the full unrestricted source-level all-K assertion from an earlier explicit theorem construction plus a published modulo pair and the population coefficient identity. No optimization, new compatibility theorem or unproved limit is left.

### Joint density and six positive distances do not rescue family credit

The singular witness above already settles the unrestricted source question. Even the stronger regularity/positivity assertion has a complete routine smoothing bridge, so it is not a surviving new family under the counting standard.

Fix K and j so the three violations have positive margins. For dyadic q tending to infinity, condition on the three q-bin indices of `(A,B_j,C)` and independently resample each coordinate uniformly in its own bin. The common mass array

    p_abc=P(A in bin a, B_j in bin b, C in bin c)

defines a density `q^3 p_abc` on each cube. Marginals stay uniform. Each pair is exactly its bivariate checkerboard approximation, since summing the third index recovers its pair-cell mass. Compatibility is therefore proved, not assumed.

The public quantitative/continuity antecedent [Ansari–Wiesel2606.07354](https://arxiv.org/pdf/2606.07354), Lemma2.5, gives checkerboard convergence in the conditional-CDF L1 metric d1 for every fixed copula. Apply it to each of the three copulas AND its transpose. For h=partial_1 C, h_q=partial_1 C_q, values lie in[0,1], so

    |xi(C_q)-xi(C)| <= 12 integral |h_q-h| -> 0.

This last bound follows immediately from |a²-b²|<=2|a-b|. Thus all six coefficients converge simultaneously at fixed j. Choose one sufficiently fine q to preserve all three strict margins. This is legitimate fixed-law smoothing; it does not interchange the j and q limits or assume uniform continuity over copulas.

Finally mix that density with epsilon times the independent uniform three-cube density, using one common mixture indicator. Every pair copula becomes `(1-epsilon)C_pair+epsilon Pi`. Its conditional derivative is `(1-epsilon)h+epsilon v`; uniform marginals make the variance formula yield exactly

    xi_epsilon=(1-epsilon)^2 xi,
    d_epsilon=(1-epsilon)^2 d + 2epsilon-epsilon².

Consequently all six distances are strictly positive; average and max transform by the same affine formula. Each strict triangle defect is continuous at epsilon=0, so a sufficiently small common positive epsilon preserves all three. This gives a jointly absolutely continuous uniform triple with the strengthened positivity property. No exact r97 n-bin formulas are asserted to follow unchanged. The formulas are a particularly convenient explicit witness in an already settled-by-reduction family.

### Why this reverses the preliminary objection

Fuchs–Wang alone does not give near-mutual adjacent edges. Bücher–Dette's weak shuffle density alone does not transfer xi or solve compatibility. Those criticisms remain correct. The missing evidence is the **different** old theorem that shuffles a one-way deterministic pair toward full Sobolev norm on the original probability space. An arbitrary bijection of a conditioning variable preserves forward xi but may change reverse xi because the latter treats that variable as target. Restricting attention to increasing transforms misses exactly this mechanism. Theorem5.4 exploits it quantitatively and explicitly; the compatible triple is the original variable, its invertible shuffle and its original image.

Rockel2505.08045v2, May22,2026, Proposition3.3 and its pp25–26 proof give an additional exact checkerboard/check-min correction `m tr(Delta^T Delta)/n`; these passages were read and saved. They confirm that within-cell randomization is an established quantitative operation, but do not by themselves select the triple. Its Theorem4.2 lower bound assumes MTP2 and is not invoked for our arbitrary copulas. Ansari–Fuchs2503.11390v2 Lemma2.1/Theorem2.2 require conditional-copy convergence; their ordinary weak-limit counterexample was also read. The all-pairs checkerboard bridge above supplies the needed stronger convergence directly.

**Substantive verdict: FAIL for campaign discovery eligibility, with an explicit old-body reduction.** This does not dispute correctness, independent invention, usefulness of exact formulas, or that CGK later described approximate variants as open. An open label can coexist with an overlooked older reduction. No worldwide priority claim is needed to apply the campaign rule excluding routine corollaries.

## Current registries and chronology: bounded observations

Fresh lawful API reads at19:54:08–09 UTC: Omega `c9cea079996532f43216352b68960a727b7ed8fe` (head commit19:52:45); OpenAI unchanged `7ef5c0cc5ca4b0e072b7a050fca09ab24bc6fa3a`. Responses and pinned raw bodies are hashed in `http-receipts.json`. Omega9aef-to-current comparison reports ahead21/behind0 and nine net changed files. Its commit list includes earlier-authored theta-tail work merged now, so head/merge time does not establish time of origin. This is not the truncated300-file aggregate comparison and is not claimed to cover every transient change inside those merges.

I inspected the current actual Blueprint ThetaTailRobinWitness theorem/commentary (conditional RH/actual theta integral/Robin integer witnesses), AURIC v18 Definition3.1/Theorem3.2 (five-dimensional CPTP channels preserving three occupation projections imply Schur multipliers), and FIB Section33 Definition33.1/Theorem33.2 (phase-event-reset finite hidden producers have d(P)<c-star via finite phase-type rows). The latter's d is a spatial risk, not 1-xi; its common hidden-law requirement is not a uniform copula triple result. These are substantive object comparisons, not absencegrep. Other sections have only table-of-contents/selected scope coverage, not full proof audits.

Inherited complete18:13 inventories Omega1b999/OpenAI7ef5 are preserved. The prior28414-to9aef214-file comparison and preliminary selected PARITY posterior-cumulant body remain bounded evidence. Complete path inventories do not constitute complete semantic proof coverage; the older large aggregate300-cap does not become complete by adding this delta. Neither the unchanged OpenAI head nor my search results certify worldwide novelty. Those limitations remain candid but do not undo the positive earlier-body subsumption established above.

## Resolved and remaining gaps

Resolved: frozen identity, an independent coauthor manuscript route and exact text comparison, source accepted-manuscript multiplicative interpretation, the previously missing compatible-triple old-object bridge, lawful quantitative smoothing preserving common joint law and six positive distances, and dated current head/delta/body observations.

Remaining: final published CGK body not obtained/compared; exhaustive registry/bibliography semantics and absolute historical priority not certified. These do **not** require another generic eligibility review or repeated blocked-source requests to make this bounded disposition concrete. Recommendation is exclusion from discovery credit now on the complete old-body reduction, preserving VoR/source hold as a separate fact. No Lean/paper investment recommended; no counts edited.
