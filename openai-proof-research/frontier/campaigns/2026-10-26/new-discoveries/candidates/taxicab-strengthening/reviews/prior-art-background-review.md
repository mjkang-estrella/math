# Independent taxicab prior-art and source-scope review

Date: 2026-10-26. Reviewer: polynomial lane. This review is independent of the parent scalar-proof construction. It does not certify absolute novelty or add a discovery to the tally.

## Verdict

The precise 2020 taxicab conjecture is a substantive and correctly identified target. No prior proof of its unrestricted lower bound was located in this review. There is positive historical evidence that the unrestricted case remained open after the 2018 normed-space paper: the published 2020 article both cites that paper and explicitly poses the unrestricted result as Conjecture 1. Nevertheless, I could not inspect the full 2018 primary paper, so a complete theorem-by-theorem exclusion of that closest prior work remains outstanding. Search-result abstracts alone cannot close this gap.

The known upper bound/sharpness example at ratio 3/2 must receive prior credit. Do not present either the constant or the existence of such an example as newly discovered. The possible new result is the universal lower bound, together with its independently constructed proof.

Do not use the L1 result alone as an unqualified refutation of Kurusa's 2024 Conjecture 7.3.9. Its explicit scope requires additional care, explained below. This would in any event be the same mathematical discovery, not a second outcome.

## Exact primary target

Maja Petrović, Branko Malešević, and Bojan Banjac, *On the Erdös–Mordell inequality for triangles in taxicab geometry*, Journal of Mathematical Inequalities 14(4) (2020), 1299–1319, DOI [10.7153/jmi-2020-14-84](https://doi.org/10.7153/jmi-2020-14-84). The [published full article](https://files.ele-math.com/articles/jmi-14-84.pdf) is publicly available. I independently downloaded it and visually inspected printed p. 1318.

Conjecture 1 on that page concerns every interior point of every triangle and asserts the 3/2 lower bound. Equations (5) and (6), printed p. 1301, define the opposite-side quantities by distances to the supporting lines: an affine linear equation divided by the maximum absolute coefficient. Equation (4) uses the L1 vertex distance. Thus the current explicit coordinate Lean definitions match the published conventions. A general-coordinate supporting-line theorem addresses the source's orientation gap. A claim about distances to closed side segments would require its own bridge.

The immediately preceding theorem treats restricted coordinate positions. The authors explain why rotation is unavailable as a reduction in taxicab geometry. This is not a wording correction or a degenerate-boundary counterexample.

The independently refreshed MathDB 341671 API snapshot has status `open`, no listed solutions, no comments, and no human solves. This records the database state on review, not an authoritative guarantee of current mathematical novelty.

## Closest prior work and the 2024 survey

Mostafa Ghandehari and Horst Martini, *On the Erdős-Mordell inequality for normed planes and spaces*, Studia Scientiarum Mathematicarum Hungarica 55(2) (2018), 174–189, DOI [10.1556/012.2018.55.2.1392](https://doi.org/10.1556/012.2018.55.2.1392). The first author's name is Mostafa. The publisher full text was unavailable; no public author manuscript was found. No access controls were bypassed and no paid document was purchased. The abstract's general extension claim does not specify the optimal constant.

Árpád Kurusa, *Metric Characterizations of Projective-Metric Spaces*, in *Surveys in Geometry II* (2024), pp. 225–256, [official chapter](https://link.springer.com/chapter/10.1007/978-3-031-43510-2_7). I read the authorial text through the [user-supplied readable copy](https://dokumen.pub/surveys-in-geometry-ii-2024nbsped-3031435095-9783031435096.html), especially §§7.2.1.2, 7.2.2, and 7.3.4. Its public HTML garbles some displayed mathematics; no claim relies on the malformed square-root typography.

The survey credits the 2018 paper with a lower estimate involving the minimum and maximum Euclidean radii of the unit ball. It also attributes an L1 configuration of ratio 3/2 to that paper's Figure 3. Conjecture 7.3.9 proposes equality for the plane's infimum ratio. However, §7.2.1.2 explicitly requires a strictly convex symmetric unit ball, excluding the L1 diamond despite its later illustrative use. The side-distance terminology also needs checking against supporting lines versus segments. These qualifications prevent an immediate formal refutation claim from the L1 theorem alone. Euclidean radii additionally depend on the auxiliary Euclidean coordinates, whereas the metric ratio is preserved by linear isometries between normed planes. Any interpretation of that conjecture must specify normalization. For the standard diamond the radius quotient yields a lower estimate of sqrt(2), strictly below 3/2; this comparison is elementary, not evidence of a prior unrestricted 3/2 theorem.

## Search extent and remaining limitation

Searched exact and accent-varied titles; DOI; Ghandehari/Martini with Mordell, normed, PDF, repository, UTA, and Chemnitz; taxicab/Mordell with conjecture, proof, solved, 2025/2026, and Patel; Kurusa's exact chapter title and Erdős ratio. Checked public bibliographic records and UTA's open technical-paper archive. Author-homepage and publisher access failures were retained as limitations. No purported inaccessible theorem was inferred from snippets. No relevant unrestricted resolution was found, but absence of hits is not proof of absence.

Recommended paper language: “We give a proof of Conjecture 1 of Petrović–Malešević–Banjac. Their restricted-position theorem and the earlier work of Ghandehari–Martini are prior results; the latter already supplies a sharpness example, as recorded by Kurusa. We have not located an earlier proof of the unrestricted lower bound.” Do not claim a first proof in all normed spaces without reviewing the full 2018 statements.

## Audit material

Local files are research-only source snapshots, not a redistribution license:

- `sources/jmi-14-84-published.pdf`: SHA256 `18c64799f9f65b475588324851e43abf409ad00d3222b2e7bad022db636070a4`.
- `sources/jmi-14-84-published.txt`: searchable extraction.
- `sources/jmi-14-84-p1318.png`: visually inspected Conjecture 1 and bibliography.
- `sources/341671-review.json`: SHA256 `3c2b701ada3831360ab0392808dda85cbcd77e4b41b08f6981e4f28577f53e42`.

The standalone supporting geometry module remains `formal/TaxicabGeometry.lean`, SHA256 `b8a8ec0fc3c3f67f351ad28b2417dbdaec10946aea5f749f205c11e5973160f0`. Its pinned-kernel audit passed all 32 declarations with only the standard foundational axioms. See `GEOMETRY-BRIDGE.md` and `geometry-audit/build/audit.json`. This audit is a proof-correctness check, not a novelty certificate.
