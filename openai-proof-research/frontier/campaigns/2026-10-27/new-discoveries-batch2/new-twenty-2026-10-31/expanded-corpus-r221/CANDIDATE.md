# No qualifying new candidate

No target in this reservation is submitted for acceptance. Six targets are excluded by prior exact results; fourteen remain parked. No new Lean source, theorem, axiom audit or clean replay is claimed.

## 368314: independent reproduction, excluded before formalization

The strongest finite hit was genuine mathematically, but already public. On the product order `[3] × [12]`, take the interval-closed set

`{(1,6),(1,7),(1,8),(1,9),(1,10),(1,11),(2,5)}`.

Apply toggles in reverse row-major order, using the source rule: toggle membership exactly when the new subset remains interval-closed. Its orbit has 73 distinct members and total signed cardinality 1. The rank is the sum of the zero-based coordinates; the even-rank weight is 1. Thus the orbit average is `1/73`, contradicting the reserved zero-mesy assertion.

The C search uses a missing-point convexity test: a subset is convex iff no absent point has both a selected predecessor and a selected successor. Its incremental toggle test checks immediate neighbours; the independent Python verifier instead tests all comparable endpoint intervals after every proposed toggle. The two implementations agree on all 73 transitions, including the return, and on the nonzero integer sum. The full certificate data are in `outputs/orbit-12-67552.json`.

**Novelty veto:** Omega already has exactly this target refuted in `D5/S3/Combinatorics/Geometry/IntervalClosedSignedCardinalityRefutation.lean`, introduced at commit `58ecb855708155edd05871ad8141f748de45237b` on 2026-10-04. Its `claim` quantifies over both source dimensions, every admissible chain length, every complete reverse extension and every order-convex initial set. Its `result : ¬ claim` proves a 73-state signed sum of -1. The independent +1 orbit is its sign-paired counterpart. The actual current body and commit receipt are retained. No additional n, parameter family or formalization of this already refuted target can count.

The initial registry path search included `rowmotion` and `homomesy`, but missed the differently named `IntervalClosedSignedCardinalityRefutation` file. Exact-hit literature search and the expanded keyword screen caught it before any Lean investment. This limitation is explicit in `results.json`, rather than presented as prior clearance.

Primary sources: [source conjecture](https://arxiv.org/abs/2307.08520), [follow-up](https://arxiv.org/abs/2505.04000), [public exact refutation](https://www.trureturing.org/research/elder-lafreniere-conjecture-4-12-signed-cardinality-refutation/).

## Sustained 368114 matching route: parked

The literal problem allows disconnected unions provided at least one component is not K4. The search deliberately sought independent connected obstructions, without starting from the source's K4 disjoint union or switching its edges. A proper three-coloured cubic graph on 2n vertices is represented by its three disjoint perfect matchings. With M1 fixed, M1 union M2 is a union of alternating even cycles, parametrized by a partition of n into parts at least 2. This classifies M2 up to the stabilizer of M1. For each cycle type the program exhaustively generates every M3 disjoint from both.

A memoized recurrence chooses the least remaining vertex: either leave it uncovered (two uncovered vertices total) or match it using each allowed incident edge. It collects every achievable colour-count vector for matchings of size n-1. Coverage and exact counts are in `outputs/matching-exact-{12,14,16}.json`. Orders 12 and 14 are complete for connected properly three-coloured simple cubic graphs under this representation. Order 16 is incomplete: only a prefix of M3 at cycle type `[2,2,2,2]` was checked before the 100-second internal stop. No violation appeared. Separate reproducible random samples covered even orders 8 through 24.

The source's all-K4 parity obstruction and the campaign's two-switch exclusion 381751 remain vetoes. No statement about disconnected cases, minimal counterexample order, or the truth of the conjecture is inferred from the connected checks. A future route needs either an independently motivated disconnected colour-profile obstruction that survives the construction veto, or a uniform theorem. Neither is supplied here.

## Other concrete routes: parked

- **367984:** Five triangulated spheres were sampled at orders 30, 30, 32, 36 and 40, beyond the authors' complete verification through 28. All have minimum degree 5. Edge subdivision with two opposite neighbours followed by admissible edge flips maintains the triangulated-sphere carrier; combinatorial Euler and circular-link checks independently pass. Each edge's two opposite facial vertices supplies one candidate crossing edge. All 474 raw additions were 4-colourable. Every SAT assignment satisfies every CNF clause. These are five sampled embeddings, not all graphs of any order and not 474 nonisomorphic graphs.
- **368836/368837:** Exact subset DP computes chromatic and clique numbers, hereditary perfectness and perfect maximum-clique transversals. All 1,253 atlas graphs through order 7 and 4,883 independently sampled graphs of orders 8 through 13 were perfectly divisible. This leaves the conjectures open. The source's Figure 1 refutes an earlier proof step, not Conjecture 1.2; it was not used to manufacture an obstruction. The missing structural step is compatible division across a clique separator, respectively treatment of the remaining P5-free atoms.
- **368265:** Ten explicit twisted triangular grids include examples with 1,394 and 1,426 triangular faces, beyond the census face limit. Propagating a tentative automorphism from each oriented base-face image found no transitive action on faces. This is a restricted quotient family, not a classification of all Klein triangulations or a formal topology certificate. A global argument would need to control all vertex-face types, not just equivelar grids.
- **368382:** Six SAT constructions produce literal Latin-square realizations of mixed-size partitions at the largest-part bound. Each square, all subsquares and every SAT clause were independently checked. These are instances only. A rational outline with denominators cleared yields a scaled statement; using that as the original undilated all-partitions theorem would be a scope error. No new result is proposed.

## Other exclusions

- **367655:** its own Venn-diagram source already disproves the Pruesse–Ruskey conjecture.
- **367789:** its own spanning-tree-model source states and proves the torsion conjecture.
- **367794:** Fox–Tidor, SoCG 2026 Corollary 3.9 explicitly proves a stronger separator theorem; its primary PDF and proof context were read.
- **367832:** its own Theorem 4.3 proves the finite four-point characterization.
- **368492:** current Lean Pool lists and includes an exact refutation at every base size, including primitive groups. The actual `Examples/MainTheorems.lean` theorem and generalized Saxl definitions were read. A hypergraph common neighbour is a common neighbour in its two-section, so this matches the reserved target.

## Qualification limits

Every reserved statement and primary target context was read. Not every proof body, older version, thesis, erratum or citing paper was inspected. Downloading a version is not asserted to mean auditing it. GitHub searches are repository searches, not exhaustive semantic code search; registry trees are path screens except the positive bodies specifically read. No current MathDB solution-state certification is claimed. These restrictions prevent novelty clearance for the parked targets and are not evidence of their resolution.
