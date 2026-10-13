# I212: independent contribution review of the tetrahedral lower bound

2026-10-12. **CONTRIBUTION SUPPORTS NOMINATION**, with the comparison and novelty limits below. This is a contribution disposition only, conditional on the separate proof gate. No finding is accepted or counted by this review.

The supported nomination is one connected result: the exact lower bound

    sum_i |B_i| >= (sqrt(15)/9) A_min(T)

for every finite cover of a regular tetrahedron by cylinders with arbitrary measurable finite-area perpendicular bases, supported by the exact optimum within nonnegative polynomial densities of degree at most two. The certificate optimum is not a second substantial finding. Neither actual covering optimality, optimality among all densities, an improved upper cover, nor a dependence on I203 is part of the supported claim.

## What is old, and what is the proposed advance?

The density argument is old. Bezdek–Litvak 2009, Theorem 3.1 and its proof, explicitly use a nonnegative density and integrate it along cylinder axes. Their general theorem gives the directionwise ratio lower bound 1/3 in dimension three and the stronger ball/ellipsoid result 1. Their 2016 follow-up, Theorem 3.1, extends this to multiple covers but gives 1/3 again for a single arbitrary-body cover. Its other main inequalities concern packings, not stronger lower bounds for tetrahedral covers. Both papers were read in full, from their primary PDFs. [2009 primary paper](https://arxiv.org/abs/0903.4842v1); [2016 paper, reviewed v2](https://arxiv.org/abs/1507.05115v2).

The broader analytic framework is also old. Falconer 1980 studies mass maximization under uniform bounds on sectional integrals; Corollary 5.4 explicitly averages over regular-simplex symmetries. Those sections are hyperplanes, so in dimension three they are planes, whereas I209 constrains lines. His simplex corollary does not state I209's line bound. Akopyan–Karasev–Petrov 2014, Section 7.1, explicitly describe fractional-covering duality and density arguments for balls. Their Theorem 7.1 concerns ball covers with two-dimensional axes; the line-axis ball case is the earlier Bezdek–Litvak theorem. Neither is the claimed tetrahedral calculation. [Falconer](https://doi.org/10.1017/S0305004100056553); [AKP, reviewed v1](https://arxiv.org/abs/1404.0871v1).

Thus there is no novelty credit for Tonelli/Fubini, mass divided by maximum line integral, symmetry averaging, or one-variable differentiation. The basic endpoint inequality is elementary too: for centered edge-two vertices with off-diagonal scalar product -1/2, convex combinations satisfy

    p.q = 2 sum_i r_i s_i - 1/2 >= -1/2,
    |(p+q)/2|^2 - |p-q|^2/4 = p.q.

Calling this alone a new geometric principle would exaggerate the contribution.

The candidate's additional content is the **sharp all-line weighted envelope**, including its opposite-edge equality family, followed by the quantitative covering consequence. The pinned companions' ordinary identity A(u)L(u)=3 vol(T) controls maximum unweighted chord length in a direction. It supplies neither the midpoint-versus-length constraint with equality nor the weighted maximum. As a diagnostic, using only length <=2 and midpoint radius squared >=0 at a=19/10 gives a certificate of just 16/47, not sqrt(15)/9. A parameter choice in that old unweighted estimate is insufficient. Once the new weighted envelope has been established, choosing 19/10 is routine; it must not be counted separately.

The proposed optimality over all nonnegative quadratics has a meaningful scope: a nonsymmetric quadratic is included through finite-group averaging, which preserves mass and cannot increase the uniform line-integral bound. The resulting alpha+beta|x|^2 family and its exact maximum then give the full stated class, not merely a trial radial family. This supports the lower theorem's completeness; it is not evidence of general density or covering sharpness. Uniqueness of nonsymmetric maximizers is not claimed.

## A stronger old baseline must be acknowledged

The submission compares with 1/3, but an immediate consequence of the **same 2009 primary theorem** is stronger for a regular tetrahedron. In the edge-two normalization its inradius is 1/sqrt(6): its altitude is 2sqrt(2/3), and its centroid is one-quarter of that altitude from each face. Any cover of T covers this inscribed ball. Applying the ball theorem to the same cylinders gives

    sum_i |B_i| >= pi/6,
    sum_i |B_i| / A_min(T) >= pi/(6sqrt(2)).

This is a deduction from the old theorem, not a claim that a source separately advertises it as a tetrahedral record. It is about 0.37024, compared with sqrt(15)/9 about 0.43033. The proposed bound remains strictly stronger: their ratio is 2sqrt(30)/(3pi)>1. The elementary bound pi<22/7 suffices to check the strict inequality. The relative increase over this stronger baseline is about 16%, rather than the approximately 29% increase over 1/3. These decimals describe exact inequalities; no numerical experiment was used.

No stronger applicable tetrahedral lower theorem was identified in the actual primary statements reviewed. This is a bounded comparative finding, not an assertion that all prior literature has been exhausted.

## Substantiality and normalization

This is a quantitative advance on the absolute cylinder-covering extremal problem for its classical regular-tetrahedron example. Bezdek–Litvak's introduction explicitly identifies that example and the half-minimum-shadow question. Verreault's survey, Question 4.14 and its adjacent discussion, records the same question and 1/3 comparison. I read that discussion directly; the survey's pre-corpus statement that the half-bound remains open is superseded here by the stipulated pinned upper constructions. [Survey, Question 4.14](https://arxiv.org/html/2203.05540v2).

The pinned angular theorem gives a strict upper endpoint below 1/2. Moving the lower endpoint from even the stronger insphere consequence pi/(6sqrt(2)) to sqrt(15)/9 narrows a genuine extremal interval for this body. It is not a local integral without a covering consequence, nor a reparameterization of the paid upper construction. The derivation is short and elementary, but that does not eliminate the size or mathematical relevance of the improvement. This is the reason for supporting substantiality.

For clarity, put R=sum_i |B_i|/A(u_i) and S=sum_i |B_i|/A_min(T). Always R<=S. A lower bound on S does **not** imply the same lower bound on R. An affine map multiplies each cylinder's base area and its own shadow by the same factor, but this factor depends on the axis. I209 therefore does not improve the affine-invariant directionwise 1/3 theorem for all tetrahedra. This narrower scope is a limitation of the contribution, not a defect in its stated formulation.

## Independent scrutiny and remaining objections

I sought a source already supplying the exact constant, weighted envelope, or a stronger applicable bound. The review included exact and equivalent constants, weighted sections and density formulations, regular-simplex results, the Bezdek–Litvak follow-up, and fractional and symplectic cylinder statements. Detailed queries and exclusions are in the literature record. Search failure itself supplies no novelty evidence. The positive basis for this disposition is the actual comparison of hypotheses and conclusions above with the candidate's additional all-line estimate.

The following limits remain:

1. **Worldwide priority is not certified.** No exhaustive citation graph, all-language search or survey of every convex-geometric density problem was performed. “New in the reviewed corpus and primary comparisons” is supported; “first known” or “best known worldwide” is not. The identified methods themselves are demonstrably old.
2. **The stronger old baseline should enter the final presentation.** An account saying that 1/3 was the only available consequence of prior results for a regular tetrahedron would be misleading. This correction does not erase the new quantitative gap.
3. **Bang's original paper remains unread.** The AMS request returned HTTP 403. Historical attribution relies on the directly read primary accounts of Bezdek–Litvak and the bounded survey discussion, not an alleged reading of Bang.
4. **No separate proof disposition is issued.** I inspected the endpoint mechanism, equality-family role and symmetrization to identify the claimed new content and plausible overstatements. The assigned independent proof gate must settle mathematical validity. I do not certify the failed upper route, its estimates, or I203.

Subject to those explicit limits, I found no contribution objection requiring reduction to TECHNICAL/KNOWN ONLY. Support concerns exactly one lower-bound theorem with its quadratic-certificate sharpness. It does not authorize a count increment or broaden the theorem's normalization.

## Reading and conduct limits

The I209 brief, full report, full analytic record and literature note were read as supplied in the user message. The report and analytic record were not re-read from disk; their disk hashes are identified as digest-only in the authentication record. Existing primary sources were read in place. The four companion introductions, both retained projection appendices, retained rational and singular sections, the angular cubic section, and the ruled-source comparison and bibliography were read in full. This does not constitute a full read of all four manuscripts or their referenced input files.

All 14 pages of Bezdek–Litvak 2009, all 14 pages of their reviewed 2016 v2, all 16 pages of Falconer 1980, and all 15 pages of AKP v1 were read through text extraction. Falconer's embedded mathematical glyphs have extraction defects; the legible definitions, section dimensions and theorem/prose scopes suffice for the comparison, and no audit of its numerical formulas is claimed. Verreault was read only in the explicitly recorded HTML excerpts, not as a complete survey. Exact file hashes, page ranges, catalogue truncation limits and retrieval failures are in input-authentication.json.

No other active review was read. No subordinate agents, research code, tests, numerical or parameter scans, snapshots, seals, historical replay, shared or ancestor edits, staging, commits, or publication were used. Only the assigned review, authentication and literature files, and the three fully read new primary PDFs, were written. Detached final hashes accompany the handoff.
