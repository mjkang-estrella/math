# Report — fresh-structural-discovery-r135 (packet public copy)

Provenance: Factory Droid / claude-opus-5-5 / high. Authorized mathematical discovery, round r135,
2026-10-20. Pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb stipulated true (not audited). No
self-gates: no correctness/contribution verdict, no acceptance, no count, no priority claim is
assigned here.

## Status
FROZEN_AUTHOR_PROOF_NOMINEE — full scope, frozen before proof drafting.

## Frozen claim (packet/public/frozen-statement.md)
For all positive integers m, n, with d_r = floor(r/2)·floor((r−1)/2):
(1) every drawing of K_{m,n} in which adjacent edges cross an even number of times has at least
    d_m d_n unordered pairs of edges that cross an odd number of times;
(2) the balanced-axis drawing witnesses exactness (no adjacent crossings, at most one crossing per
    pair, exactly d_m d_n crossing pairs).
Consequences frozen with it: the weakly-semisimple odd, semisimple odd, and semisimple pair
crossing numbers of K_{m,n} all equal d_m d_n, hence (quoting pinned thm:main) coincide with the
ordinary crossing number on K_{m,n}.

## Proof (packet/public/proof.md)
Self-contained; the pinned theorem is quoted only for the final identification with cr. The proof
rebuilds the pinned preprint's machinery over characteristic 2: parity-preserving normalization;
a native mod-2 chord formula; a parity intersection matrix with a cycle pairing proved by a
one-sided shift with exact diagonal bookkeeping (the classical two-sided averaging divides by 2
and is unavailable mod 2); the additive block relation; the subspace intersection bound and
rank-sum corollary reproved over infinite characteristic-2 fields; the barycentric rank detector
reproved in characteristic 2, where the 0/1 strict-order matrix replaces the ±1/2 half-sign matrix
and invertibility is recovered by an additive row flip onto the two-triangle evaluation pattern;
assembly for odd n; vertex deletion for even n; the axis drawing for exactness.

## Strongest integrated reduction, and what is unpaid
The theorem does not follow from the pinned statement (ocr-type minima are a priori smaller than
cr; the pinned theorem gives only the upper bound here) nor from quoting the pinned proof over the
reals (signed sums over-count odd pairs: two same-sign crossings contribute nonzero). The general
comparison cr(G) <= 2 iocr(G)^2 (Schaefer DS21) yields only oc >= Omega((d_m d_n)^{1/2}), far
short. The unpaid operation this nominee pays is the characteristic-2 transport itself: the
one-sided shift with diagonal bookkeeping, the even-adjacent hypothesis identified as exactly the
diagonal-block condition, the field transfer of the subspace lemma, and the row-flip detector
invertibility. Prefreeze, the Harborth K_{2,m,n} direction (cr = Z(m+2,n+2) − mn) was derived to a
quantified obstruction (subgraph bounds reach about half the target; the deficit lives in
apex-star crossings an optimal drawing avoids) and was abandoned unfrozen; see working-notes.md.

## Novelty accounting (scoped, not a priority claim)
New to this project: history searches (aliases: odd crossing, iocr, pcr, pair crossing, Hanani,
parity, Zarankiewicz, Harborth, tripartite, join product, Klešč; hidden/JSON/large files included,
no size cutoff) found no prior project work on parity/pair crossing variants; R027 occupies
ordinary cr of K_n − e, and its lineage engaged Sadhu's ordinary cr(K_{m,n} − e) claim — different
operations. Not found in the literature checked (queries and read extents in reading-limits.md):
any exact determination of ocr±/ocr+/pcr+ of K_{m,n}, and any post-2026-10-06 derivation of parity
corollaries from the pinned proof. The pinned preprint (2026-09-23) explicitly restricts itself to
the point-count convention. Because the result implies the lower bound of Zarankiewicz's
conjecture (in the even-adjacent class), it could not have been proved by pre-pin methods either.
These are "not found" statements with disclosed search limits, not a worldwide-priority audit.

## Limitations (frozen)
Unrestricted ocr/iocr/pcr of K_{m,n} not determined (adjacent odd crossings break diagonal-block
control); no tripartite Harborth statements; constants/formula exactly as frozen.

## Validation
Mechanical artifact checks only (not a mathematical gate): packet/public/sanity.py passed all
checks (a)–(h), including a GF(16) detector implementation (all 6 orders at s=1; 40 sampled orders
at s=2), randomized rank-sum checks over GF(2), chord formula over all 24 orders x 4 gaps, and an
exact rational simulation of the axis drawing for 2 <= m,n <= 7. Independent adversarial
correctness review has NOT occurred; downstream stages unopened.

## Anchors
Outside report: ../../../../REPORT.md path relative to packet is REPORT.md at the round root; the
detached FINAL/MANIFEST/REPORT SHA-256 anchors are in FINAL.json / FINAL.sha256 / REPORT.sha256 at
the round root. Verifier: python3 -B packet/public/verify.py --root <round root> --project
<openai-proof-research> --finalhash <contents of FINAL.sha256>.
