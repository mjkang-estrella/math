# r101: finite biased-Snaky construction attempt

Pre-freeze exploration; no nominee or completed classification. The natural full question is the exact largest Breaker bias against which Maker, claiming three cells per turn, can force Snaky on the initially empty infinite square board. Reflections and quarter turns are allowed, scaling is not. The source shape is S={(0,0),(1,0),(2,0),(3,0),(3,1),(4,1)}. No proposed threshold value is yet asserted.

## Actual source and paid comparison

The pinned source187 introduction and strategy sections were read completely, including its actual conditional-position semantics, 21-claim global policy, and finite251-cell/17×17 board conclusion. All41 non-PDF canonical blobs were authenticated against the complete pinned tree; acquisition is not full reading. The source's entire compiler/certificate was not replayed. Parent r6 already studied the strong-game race; this attempt does not reuse that target or infer a strong-game victory.

Norris–Sieben, Biased Weak Polyform Achievement Games, arXiv1107.1878, actual text118–330 (complete Theorem3.1 proof and Corollary3.3): Theorem3.1 combines bounded (a_i→a,b_i) strategies into an (a,b+s−1) strategy, where a=sum a_i,b=sum b_i. Corollary3.3 gives its equal-component specialization. Thus source187 immediately gives the balanced (2,2) result, indeed (2,3), and (3,5). These transfers are paid and technical; they were closed before a proof round.

Actual text80–110 proves Proposition2.1: after each Maker batch, Breaker may occupy its entire exterior nearest-neighbor boundary, of size at most4a. Since a<6, no single batch completes Snaky and no later batch can attach to an earlier batch. Hence Maker3 loses against12. The exact threshold is currently only bounded between5 and11. Actual text674–702 includes the size-four comparisons; no stronger three-stone upper bound follows from the straight tetromino subanimal.

The same source family is being reused, but the unpaid operation is a new finite strategy/defense for a different biased game. Same-family membership neither establishes novelty nor automatically excludes it. A classification furnished solely by subanimal comparison plus distributed-board composition would remain technical.

## Fixed response graphs: sound rule and universal degree-two obstruction

Suppose a graph on the lattice has maximum degree d. After each batch of three new Maker cells, Breaker can claim all free graph-neighbors of those cells, spending at most3d cells, and use any remaining budget arbitrarily. In a completed target, endpoints of every graph edge must have been claimed in the same Maker batch: the later endpoint would otherwise have been blocked after the earlier endpoint. Consequently every connected component of the graph induced on the target must fit into one batch. If every Snaky copy induces a component of at least4 vertices, this yields a (3,3d) defense.

No degree-two graph can satisfy that sufficient criterion, even without periodicity or a geometric edge restriction. Discard edges whose displacements do not occur between two Snaky cells. For each of the eight orientations, count translated occurrences of any fixed unordered edge. Summing over orientations, the maximum count is20, attained at horizontal or vertical unit displacement. The other counts are at most8; the explicit finite displacement table can be independently recomputed from the six coordinates. Every induced component of size4 requires at least3 edges. Consider all8 orientations translated by the100×100 origins {0,...,99}². They require at least240000 target-edge incidences. All their vertices lie in[-4,103]², with11664 vertices. An induced subgraph of maximum degree2 has at most11664 edges, each participating in at most20 of the chosen targets. Thus incidences are at most233280, contradiction. This refutes this response-graph mechanism, not the full (3,6) defense question.

The periodic degree-three response-graph searches at periods2 and3 returned UNSAT. These are bounded solver outputs with no extracted proof certificate and are NOT universal impossibility proofs.

## Priority defense test

A stronger sufficient local rule orders the four nearest neighbors at each cell. For each newly claimed Maker cell, Breaker marks the first two entries not already Maker-owned, ignoring entries already Breaker-owned; it spends at most six actual claims. Wasting unused quota is harmless. To test a putative final Snaky, regard all outside cells as free, which maximizes their ability to distract the responses. If a target neighbor v of u precedes the second outside neighbor in u's priority order, then v must have been claimed no later than u. Every strongly connected component of these temporal prerequisites must be claimed in one batch. The target's nearest-neighbor graph is a six-vertex path, so a component of size4 is equivalent to three consecutive bidirectional prerequisite edges. This gives a finite sufficient condition for a priority defense. Periods2,3,4 returned UNSAT; no assertion beyond those bounded searches is made.

## Accelerated conditional cards

In the (1→3,2) game Maker normally claims one cell, but may use three cells on the terminal turn; Breaker claims two. A conditional card has required Maker set A and Breaker-free envelope T. Base cards take T to be a Snaky copy and any three of its cells as A. Maker can then finish immediately using at most three cells.

A sound sufficient combination rule is: choose a pivot p and finitely many child cards whose requirements lie in A∪{p}; include p and all child envelopes in T; and require that no set of at most two cells outside A∪{p} hits every child envelope. Maker claims p (or a fresh replacement if already owned), then any legal two-cell Breaker reply leaves at least one child envelope clean. All prior Breaker marks are excluded by the parent envelope. This is the source's conditional-card composition idea with a two-cell transversal condition. It is a proof-tree method, not claimed new in itself.

Exact first-level generation used three terminal residual target envelopes pairwise disjoint outside four owned cells. It produced3380 sufficient rules and31 canonical required-triple patterns. After inclusion pruning, the families at a straight triple and an L-triple have no two-cell transversal outside the required triple. This yields conditional cards with two required cells after claiming the third. Deterministic random deletion of unnecessary children gives smaller sufficient envelopes; it is not exhaustive optimization. The generated adjacent-pair, distance-two pair and diagonal-pair envelopes have not yet combined to an empty requirement. Further bounded closure is exploratory, not a full strategy certificate.

Independent finite screens: every possible initial three-cell set relevant to a two-turn Maker3 win is contained in a target, giving11 symmetry types; their residual completion families have transversal at most2. This excludes a two-turn win against two or more Breaker cells, not a longer win. Among136 relevant four-cell configurations with terminal budget3, the2×2 square uniquely maximizes the transversal at8. Increasing its terminal budget to4 still gives transversal8 (64 targets); it does not improve the paid Maker4 lower bound7. These are diagnostic finite computations, not independent reviews.

## Limits and provenance

The exact three-stone threshold is not proved. Conditional winning cards requiring old stones and clean envelopes are not substituted for an empty-board result. No frozen full theorem has been narrowed. No source theorem was audited. No mathematical or contribution review has been dispatched. Temporary Z3 was installed under /var/tmp after a default pip temporary/cache quota failure; no global package or shared repository file was changed. Z3 UNSAT outputs are search evidence only. All third-party bodies are private, with retrieval hashes; public scripts contain original finite geometry and sufficient-rule checks. Source187 history and closest primary support the explicit comparisons above, not worldwide novelty clearance.


## Extended finite closure outcome

Ten further bounded closure rounds were completed. New distance patterns appear, but no family removes the one-cell or zero-cell requirement. At the adjacent pair A={(0,0),(0,1)}, the three surviving two-cell cuts are {(-1,0),(1,0)}, {(-1,1),(1,1)}, and {(0,-1),(0,2)}. Each meets every envelope outside A in the generated family. These cuts are obstructions to THIS generated sufficient family, not a history-dependent defense or a universal obstruction to accelerated strategies. Random child pruning is bounded and non-exhaustive; larger search or different rules could change the outcome.

The square residual-hitting number8 now has a solver-free certificate: eight pairwise-disjoint three-cell residual targets give the lower bound, and an explicit eight-cell transversal hits all64 targets with at most four missing cells. square-eight-packing.json records both. The exact finite support result is not nominated as a substitute for the full threshold.

An initial auxiliary Z3 installation failed because the default temporary/cache location exceeded quota. Retrying with TMPDIR=/var/tmp and no pip cache succeeded under /var/tmp/r101-python. This installation failure is not a failed theorem or a passing diagnostic. No shared package directory was changed.
