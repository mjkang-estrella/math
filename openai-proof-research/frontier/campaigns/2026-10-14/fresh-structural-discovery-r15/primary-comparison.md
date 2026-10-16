# Operation-level comparison and contribution limits

Myeongjin Kang; no affiliation. Original prose CC BY 4.0.

The frozen LR assertion is the negation of the known linear intersecting
Ryser assertion, explicitly stated in the 2021 primary paper. We do not
claim a new conjecture. Pinned family162 settles the unrestricted
intersecting covering assertion by counterexamples, but its pair
agreements need not be unique. Solving LR would decide a remaining
structural restriction, with a concrete additional construction burden.
No such solution is claimed here.

## What the established operations actually pay

1. The pinned balanced merge/split construction pays intersection by
replacing lost split-line agreements with merged-pair agreements. Its
occupancy/pencil analysis pays the lower bound against ALL q-label covers,
not merely monochromatic or same-part covers. The extension companion
uses different field orders and exceptional configurations. The graph
transfer is already cor:tree-cover in BOTH manuscripts; it is not proposed.

2. FHMW Lemmas2.1-2.2 prove minimum degree and maximum degree restrictions
on a linear tau=r example; Theorem2.3 gives a discriminant restriction,
and Theorem2.8 handles r<=9, using computation at9. Theorem3.1 gives a
linear13-partite example with13 vertices per part whose every edge-minus-one
set fails to cover, while its displayed9-cover shows why that local failure
is insufficient. Thus checking just those restricted covers cannot establish
LR. We did not run the primary computations or claim their bounds anew.

3. Bahmanian's actual Theorem4.1 is a fair detachment theorem. Its A1-A2
balance vertex degrees (also within colors), and A3-A4 balance multiplicities
of entire edge patterns across subvertices. The two laminar families in
Section5.1 implement those balances. They impose no requirement that each
pair of distinct original edges retain a common subvertex. Incidence-graph
connectivity also would not mean pairwise intersection. It would be an
additional operation to preserve intersection while splitting every double
intersection; no such consequence is available from the read theorem.

4. Ordinary affine pencils give a unique joining direction for two distinct
points. Puncturing one coordinate creates a fresh vertex and a missed line.
This classical finite-plane geometry supplies the natural alternative
construction, but does not pay its part-size/covering burden.

## What this round independently establishes

- All nonsplit line blocks in the balanced source are forced together by
unique-pair paths under ANY intersection-preserving refinement. Multiplicity
B bounds the number of non-forced neighbors, and occupancy>2B makes these
paths connected. A split pair forces a merged cross-identification; retained
points on its two constituents then force a duplicate in their actual joining
direction. This rejects every linear intersecting edge-surjective,
part-preserving lift of this source as well, by choosing one preimage per edge.
- In the separate one-fresh-coordinate pencil model, every used fresh label
injects into an unused old line label in the same part. The number of
nonisolated labels stays at most q. This holds for arbitrary ordinary subsets
and arbitrarily many exceptional edges, not just the degree-one first try.

The first checkpoint specifically addresses the unpaid intersection clause
missing from fair detachment. The second addresses the covering clause
missing from exact pencil intersection. They reject concrete operations,
rather than assuming new geometry from scalar counts. They are elementary,
source-specific support. We neither demonstrate worldwide novelty for them
nor nominate them as substantial results. Their hypotheses are much narrower
than LR and neither supplies a universal impossibility theorem.

## What remains unpaid

An actual simultaneous partition trade or other finite construction must
produce exactly one agreement for EVERY pair, while every union of r-1
blocks fails to cover the point/edge index set. The source's cover lower bound
cannot simply be inherited by vertex detachment or edge-surjective cloning,
and the pencil scheme cannot create the necessary usable part sizes. A trade
that introduces new pair agreements would require a new proof excluding ALL
small mixed-part covers; no such trade or proof was obtained. Conversely no
argument gives a cover of size r-1 for every arbitrary linear intersecting
partite system. This is the full frozen gap, not a conditional theorem or a
smaller target being advertised as solved.

The comparison is bounded to the actual primary extents recorded in
source-contracts.md. Search results for other detachment papers are not
substituted for theorem reading. No independent proof/contribution gate,
count increase, manuscript or Lean package is claimed.
