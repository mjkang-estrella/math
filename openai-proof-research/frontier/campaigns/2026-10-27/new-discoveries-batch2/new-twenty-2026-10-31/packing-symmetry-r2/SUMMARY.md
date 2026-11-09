# 340297 — parked, no solution and zero credit

The proposed refutation is NOT closed. There is new exact one-sided progress: a rational asymmetric configuration has geometric optimal area strictly below 6471/10000, by the ordinary endpoint reduction below and an exhaustive integer Python calculation. This is not a Lean certificate. No global symmetric bound or source-class minimizer-existence proof was obtained. No acceptance or ledger changes were made.

## Source fidelity

Read the actual r482 cached Bian arXiv:1809.01769v1 PDF-derived body: §§2.1–2.4, Theorem 2 and its reflection proof, Theorem 3 and its continuity proof, and additionally Lemma 5 with proof. See historical-source-receipts.json for original retrieval metadata, actual hashes and inspection timestamp. Primary URL: https://arxiv.org/abs/1809.01769 ; v1 date 2018-09-06. PDF SHA256 7c068682ea91d507a9c795af63d2b34c5aef7c7d429dee9a1be5943232f659a3; text SHA256 868d105723763b7678242d4cc877b0d3eb58e990e072707026830ee025f2ce98. Ancestor instructions, both campaign ledgers, prior-campaign-context and assigned numerical/form inputs were read; all eight input-binding hashes match (input-validation.json).

Source §2.1 has n distinct ANCHORS in the closed square, including origin; it does not assume pairwise distinct x- or y-coordinates. Each anchor receives an axis-parallel lower-left rectangle, whose interior avoids all anchors and all other rectangles. Boundary contact is allowed. Degenerate rectangles must be treated when an anchor is on an upper/right square boundary; the computational model normalizes every zero-area rectangle to its anchor point. The source does not give a separate precise degeneracy definition, so a formal endpoint must explicitly justify that convention.

Source §2.4 defines satisfaction via the actual coordinatewise partial order: P_i≤P_j iff i≤j and pi(i)≤pi(j). Its following coordinate inequalities are weak. A formalization using only sorted arrays and distinct coordinates would omit permitted configurations. Ties also must still obey the stated iff; weakly sorted arrays alone are insufficient. For the strictly ordered witness here, anchors (x_i,y_pi(i)) satisfy the iff exactly. Since pi=(4,2,5,1,3) is an involution, reflection symmetry of this strictly ordered family is equivalent to x=y. The source's indexing note is harmless for this involution; no convention for other permutations was silently imported.

Conjecture 3 concerns EVERY global minimizing configuration within the given permutation class. It does not say every locally minimizing configuration and does not merely assert existence of a symmetric minimizer. Local minimality was defined separately in §2.2. Theorem 2 only identifies the values for pi and pi inverse by reflection; it cannot turn a configuration into a symmetric minimizer. Theorem 3's continuity statement is on distinct point sets; its proof covers shared coordinates, not a license to compactify through anchor collisions.

Consequently a gap between one asymmetric configuration and ALL symmetric configurations would exclude symmetric global minimizers, but is not by itself a refutation of the conditional universal statement if no source minimizer is known to exist. Neither collision-free attainment nor full boundary exclusion is proved here. Neighbor 340296 is a different half-area target and receives no claim or credit.

## Exact asymmetric calculation and ordinary completeness argument

Use D=10^10, pi=(4,2,5,1,3), origin, and sorted coordinate numerators

x=(3574916299,4902203394,6699528833,7172681767,8786594106),
y=(3574916299,4984072088,6490568711,7292468328,8682676509).

All coordinates are strictly interior and strictly increasing; anchors are distinct. The involution property is immediate from pi(pi(i))=i. For example x_2 != y_2 proves asymmetry.

Here is an ordinary completeness proof for this STRICT witness, rather than just exhibiting a packing. Replace any degenerate rectangle by its anchor point, preserving area and legality. Keep the positive rectangles. With all their vertical intervals fixed, expand each right edge as far right as legal, one rectangle at a time. The only possible new obstructions are the square edge x=1, an anchor whose y is strictly inside the rectangle's fixed vertical interval, or another positive rectangle whose vertical interior overlaps it and which lies to its right. The obstruction x-coordinate is respectively 1, an anchor x-coordinate, or that other rectangle's left edge, also an anchor x-coordinate. Contacts at an interval endpoint are legal. A rectangle lying to the left cannot become an obstruction when expanding to the right. Thus every expanded right edge belongs to the anchor x-grid plus 1. All expansions preserve emptiness/nonintersection and increase area. Now fix these horizontal intervals and similarly expand top edges; the blocking coordinates are 1, anchor y-coordinates, and other rectangles' bottom edges, all on the y-grid. This second pass preserves the previously chosen grid right edges. Zero rectangles remain points; anchor emptiness already accounts for them. This produces a legal grid-ended packing with area at least the original packing. Hence the supremum over ALL legal packings equals the maximum over the finite grid choices. Conversely each enumerated compatible choice is a legal packing. This argument does not use the source's informal maximal-rectangle assertion.

`exact_endpoint.py` independently builds all empty positive grid rectangles for each anchor plus one zero point. It tests every compatible selection without numerical optimization or pruning. With strict grids, the index separation tests are exactly physical interior-disjointness; anchor emptiness uses strict inequalities. Option counts are 17,8,12,4,8,4. There are 106233 legal selections; 30144 have all rectangles positive. Zero rectangles are not discarded. All area sums and comparisons use Python arbitrary-precision integers with common denominator D².

Maximum = 64701496078384990463 / 100000000000000000000.

Separator minus maximum = 8503921615009537 / 100000000000000000000 > 0.

The all-positive maximum agrees with the full maximum, resolving the earlier zero-deletion concern for this particular strict witness. A maximizing selection and complete DFS counters are in exact-endpoint.json and exact-endpoint.log. Run `python exact_endpoint.py` from any directory to reproduce. This is an ordinary mathematical reduction plus exact external computation, NOT a kernel-checked all-packings theorem; no conditional Lean theorem was presented as completion.

## Symmetric bound attempt and exact remaining obstruction

The prior active weighted quadratic is indefinite. It was not reused as a PSD certificate. New numerical linear algebra on its active-difference Jacobian gives rank 2; on the resulting three-dimensional tangent space its weighted Hessian has approximate eigenvalues 0.680,2.083,2.927. Thus its negative ambient eigenvalues do not exhibit a feasible active-stratum descent direction. These diagnostics are not proofs.

A finite piecewise-polynomial route was tried: express the ordered symmetric coordinate simplex using six nonnegative gaps summing to one. Every existing positive packing form becomes a homogeneous quadratic. On a sub-simplex with vertices v_i, the coefficients v_i^T B v_j are its degree-two Bernstein coefficients, so their minimum is a lower bound for that quadratic. Maximize this lower bound over selected packing forms, and bisect the longest edge. A fixed set of 50 forms was chosen from the eight historical active indices and maximizers on a coarse deterministic simplex lattice. A subset of legal packing forms suffices for a LOWER bound; completeness of that subset is not assumed.

The initial 25000-node run and a capped 500000-node run did not close the bound. The latter took about 52.9 seconds, reached depth 48, left 162825 regions, and its remaining numerical lower bound was 0.6461906433105469 < 0.6471. Best tested center had selected-envelope value about 0.64717437. All these branch calculations used floating arithmetic and are DISCOVERY ONLY; no pruning or bound is claimed certified. In particular depth-48 floating vertex arithmetic is not an exact rational certificate. Full scripts, selected form IDs, counters and logs are retained. Enlarging this run indefinitely is not justified as a proof strategy without better bounds.

Additional structural reduction: at a strictly interior full local minimum, source Lemma 5 forces equality of maximal origin rectangles. For this permutation they have areas x_1, x_2*y_4, x_4*y_2, y_1. At a symmetric minimum, writing coordinates (a,b,c,d,e), this forces a=b*d. This reduces the necessary interior symmetric-minimizer domain but does NOT handle boundary minima or establish a bound for every symmetric configuration.

The eight historical active forms reduce to four distinct symmetric quadratics (active-symmetric-polynomials.json). Upon a=bd they reduce to just two:

F = 2ad-a+b²-2bd-2be+2b+2ce-2c+1,
G = 2ad-a+b²-2bd-2cd+2ce+d²-e²+1.

For d<e<1, F decreases and G increases in c. Their intersection has c=[2b(1-e)-d²+e²]/[2(1-d)]. Substituting this intersection gives the rational expression in reduction.log. It is only an active-stratum algebraic reduction: the intersection must lie in [b,d], other packing forms must be checked, and a global polynomial inequality over all domains is still absent. A general symbolic stationary solve was stopped after about 30 seconds; a bounded factor-only replay is reduction.py. No feasibility or global-optimality claim follows from it.

## Later primary theory, registry scope and access

Live search on 2026-11-01 UTC screened Bian title/citations and anchored-rectangle symmetry/minimizer/Freedman terms. No direct Conjecture 3 resolution was located; this is not novelty clearance. Retrieved the actual ICALP2021 Damerius–Kaaser–Kling–Schneider paper (source-receipts.json, PDF SHA256 df7312d3de907bedfff986f087ed4e835a7304770702c668a8a7afcb7af44ad1). Read §§1–1.2 definitions, related-work discussion, and Theorems 1–2: universal greedy coverage at least 39%, and an instance with greedy coverage at most 43.3%. These concern an algorithm, not fixed-permutation optimal minimizers, and do not supply our 64.71% symmetric bound or source attainment. Full charging proofs were not independently audited; no theorem from them is used in the exact calculation. Its related work points to Balas–Toth's 2016 enumeration theorem, whose exponential bound/algorithm is relevant but not a solution to symmetry. A guessed author PDF URL returned 404 (HTML saved under balas-toth.pdf, NOT an inspected paper); do not treat it as a retrieved proof. arXiv HTML v3 for the greedy paper also returned 404 in web access. No repeated forbidden requests or bypasses were attempted.

Current openai/math main head was retrieved: 4eaee87548250b2682affda7d05d947c05554bae, commit date 2026-10-30T00:35:35Z. Its pinned CONTENTS.md was fetched and screened for anchored/Bian/rectangle-packing/340297; no matching target entry found. Irrelevant Freedman/other keyword hits were not treated as matches. This is catalogue screening, not a primary-body review of the entire registry. The older immutable upstream catalogue remains distinct from this live head.

Palomar documented browse/index.json returned HTTP200 this run (880 results, 994 versions); the actual anchored API query returned HTTP403 with error 1010. Thus discovery search access remains incomplete, despite the successful index. Exact URL/date/hash/status receipts are saved. The earlier lane's blanket 403 cannot describe this run, and today's index success is not search or novelty clearance.

## Deliverable status

No literal source Lean endpoint, axiom audit, clean extracted Lean replay, or formal geometric bridge exists. None was simulated by proving only a finite model or assuming the missing symmetric bound. The files preserve a useful exact rational witness calculation and a specific failed global-bounding approach. A future attempt must first close a true global symmetric bound (or replace the separator strategy), prove collision-free source attainment or avoid needing it, and only then build and independently review the full pinned Lean proof. No mathematical discovery, MathDB solution, worldwide priority or additional accepted result is claimed.
