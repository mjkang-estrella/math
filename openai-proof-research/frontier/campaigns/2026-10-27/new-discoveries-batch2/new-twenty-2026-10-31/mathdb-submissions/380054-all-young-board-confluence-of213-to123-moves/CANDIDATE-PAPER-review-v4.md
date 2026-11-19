# A finite critical-pair proof for Young-transversal moves

Candidate research draft, not publication or an acceptance claim. MathDB 380054; source Stankova, Shape-Wilf-Ordering on Permutations of Length 3, arXiv math/0609644v1, Section 6.3 Conjecture 1. This version attaches the independent v1 fidelity review and fresh extracted replay described below. Current prior art, journal-final fidelity, raw MathDB binding, full101, registry and significance remain HOLD. Historical ordinary/v1 PASS and conditional SUBSTANTIAL are background only. Credit remains zero; counters 62/80 NEW, 101 total.

## Statement and coordinates

Let Y have n top-left-indexed rows with lengths λ₀≥⋯≥λₙ₋₁, each at most n. A cell in zero-based bottom-left coordinates (c,r) is present precisely when c<λₙ₋₁₋ᵣ. A transversal has exactly one dot in every row and column, all in present cells. A 213 occurrence consists of three columns i<j<k with dot heights p(j)<p(i)<p(k), with every selected row-column intersection present. A move exchanges the first two dot heights. An avoiding transversal has no such occurrence. A maximal finite sequence ends where no move is possible; an infinite sequence would be maximal in the other possible sense.

For every such Y and every transversal D, there is one reachable avoiding transversal E. Every maximal sequence is finite and ends at E. More strongly, any two reachable transversals have a common descendant. This statement applies to all n, including n=0, and to repeated row lengths. The paper's proper shapes are included: their staircase criterion is λᵣ≥n−r. No properness assumption is needed for the stronger theorem above; shapes lacking transversals satisfy its transversal-premised version vacuously.

The formal statement is Young213.source_shape_complete in src/YoungSequences.lean. Its sole mathematical premise after the shape data is Y.Transversal D. In particular it has no local-confluence, finite-table, oracle or certificate premise.

## Boundary and source fidelity

For each column c let b(c) be its lowest present row, or n if it has no cells. Antitonicity of row lengths implies that present rows form an upper interval, so b(c)≤r if and only if c<λₙ₋₁₋ᵣ. Narrower columns cannot have lower bottoms; hence b is monotone. This construction is RowShape.boundary, with boundary_cell and boundary_monotone proved using the least element of the finite column-row set. Empty columns use the value n and cannot contain a dot. RowShape.proper_iff identifies the source staircase criterion with b(c)≤c for all columns. RowShape.coordinates proves the one-based formula c+1≤λ at zero-based top index n−(r+1), corresponding to one-based top index n−r.

For a permutation placement p, Valid b p means b(c)≤p(c). By monotonicity of b, all nine intersections of a selected 213 lie in the shape exactly when b(k)≤p(j). Thus Legal has precisely the source's rectangle-contained occurrence condition. In particular a nonlanding 213, such as the example on source page 3, does not permit a move. The graph/transversal bijection, occurrence equivalence, step equivalence and path extraction are established by frozen YoungSource; YoungPartition constructs b from row lengths and proves the exact shape-specific equivalences. YoungEndpoint additionally proves avoidance versus terminality and preservation of literal dot transversals.

## Termination

Give p the natural-number weight W(p)=Σ_c (n−c)p(c). If i<j and p(j)<p(i), exchanging them decreases W by (j−i)(p(i)−p(j))>0. Therefore there is no infinite legal sequence. The frozen YoungTermination proves this for every n and boundary, then gives a reachable valid avoiding terminal on every monotone board. The new no_infinite_moves also proves directly that W(f(t))+t≤W(f(0)) along an infinite sequence, contradicting t=W(f(0))+1. We use this checked weighted argument and make no separate inversion-count claim.

## Local confluence: exact finite reduction

Consider two legal triples. Each full support contains three distinct columns. Their union has size three, four, five or six. Size three gives identical ordered triples and the same successor. Size six gives disjoint full triples: neither exchange changes the other's witness or exchanged rows, and the exchanges commute. This is the frozen disjoint_join branch; disjointness of just the exchanged pairs would be insufficient.

For union size four or five, compress *all six* positions, including both witnesses, using increasing embeddings e of columns and v of row values. Restriction of p becomes a permutation q. Every selected row is compared against every selected column to construct fixed rank thresholds d; these thresholds remain valid throughout a lifted path, even when witness values change. YoungSupport and YoungSupportPeaks prove these facts for arbitrary n. The new preimages_cover proves that the six preimages exhaust every compressed position: e(x) belongs to its range, which is exactly the support union, and injectivity turns the resulting six image equalities into preimage equalities.

The ordered triples on Fin 4 are 012,013,023,123; those on Fin 5 are 012,013,014,023,024,034,123,124,134,234. triples4_complete and triples5_complete prove quantified enumeration by kernel reduction. Frozen rank_coverage4 and rank_coverage5 quantify over all bijective rank functions and all pairs of indices in these lists. For 213 rank patterns that jointly cover every position, either their ordered pair or its reverse belongs to the seven four-position or 57 five-position cases. This is exhaustive finite universal verification, not sampling.

For each case, frozen Young64 supplies an actual join at the strongest monotone admissible boundary B=suffixCap(peakCaps(q,j,k,J,K)). Each initial peak, each successive move, the final equality, and the boundary formula are kernel-verified. YoungTableJoins connects membership to these joins. These files are the complete explicit finite witness component of this computer-assisted proof; no acquired script or unchecked external certificate is a premise. For an arbitrary compressed monotone board d, validity and both legalities imply d≤B by strongest_boundary. Every B-path is also a d-path. The reverse membership branch is handled using strongest_boundary with the triples reversed and swapping the resulting two paths. The separate strongest_symm lemma also proves invariance of B under that reversal.

To lift, exchange_agrees identifies both global successors with their compressed successors; valid_exchange proves both stay on the original board. Outside the selected columns, both successors equal the original placement by exchange_outside. lift_join then gives two paths ending in the *same actual global permutation*, using agreement on the support plus equality outside it. Thus local_confluence is unconditional for all n and monotone boards. Support-cardinality transport is performed by rewriting FullJoin at the proved card=4 or card=5 equality, avoiding unproved identifications of fixed finite types.

## Global confluence and sequences

Well-founded induction on the checked move relation proves equality of any two reachable avoiding terminals. If one path is empty, terminality forces the other to be empty. Otherwise join the two first steps locally, take an avoiding descendant of the join, and use the induction hypothesis on each strict successor to identify both given terminals with that descendant. Taking avoiding descendants of arbitrary reachable states now yields full confluence. Existence from termination and this equality give a unique normal form.

The shape-specific graph encoding transfers this result to literal transversals. path_sequence realizes each inductively finite path by an actual natural-indexed finite move list. Hence a maximal finite sequence exists; terminality is exactly avoidance, so every maximal finite sequence reaches the same E. Encoding a hypothetical infinite shape sequence gives an infinite permutation sequence, already excluded by the weight argument. These are all clauses of source_shape_complete.

## Formal dependencies and limits

Five new production modules supply 39 theorems: YoungIntegration, YoungGlobal, YoungPartition, YoungEndpoint and YoungSequences. They import the twelve frozen modules without edits, using exact supplied seed oleans copied only to mutable build. Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 are pinned. Every new production module compiled and passed leanchecker. Two separate audit modules compiled and passed leanchecker; the final complete endpoint's transitive axioms are exactly propext, Classical.choice and Quot.sound. All 39 new theorem axiom lines are retained in AXIOM-AUDIT-v3.json. This is checked cache reuse, not the required independent all-source rebuild.

Only the owned v1 source was used. Pages 1–3,12,24 were rendered and inspected in this run. No claim is made about the closed EJC final version, current public proof status, novelty or protected local comparisons. The candidate is ready for independent statement-fidelity review and fresh replay, subject also to the recorded process deviations. It is not accepted or publication-ready.


## Independent extracted replay and attached sources (review v4)

The separate REPRODUCIBILITY-APPENDIX-v1.md contains all 19 source modules verbatim, in uniquely named `lean module=NAME.lean` fences. SOURCE-PROOF-PINS.json binds every module byte count and SHA256. The independent extract-v1.py rejects missing, duplicate, unexpected, malformed and traversal names, verifies bytes/hashes, and supplies an initially empty src directory. Its six negative packaging tests passed. No implementation olean was supplied to this replay.

All 19 extracted modules freshly compiled and passed leanchecker in dependency order; IndependentReplayAudit separately compiled and passed leanchecker. All 40 invocations used the unchanged own 32 GiB formal wrappers, with the 6 GiB sampled group RSS guard and other caps. The complete endpoint and source bridges have only propext, Classical.choice and Quot.sound as transitive axioms. The previous paragraph about seed reuse describes the historical implementation run, not this replay. See REPLAY-AND-FIDELITY-v1.md, formal-results-v1.json and the raw formal01--formal40 outputs/receipts for exact evidence and limits.

The appendix is a packaging addition; no production theorem or source was edited. This review found no load-bearing v1 statement-fidelity or mathematical defect. It does not authenticate raw MathDB or the closed EJC final, clear current prior art/full101/registry/significance, waive any historical or review process deviation, or add credit.
