# MathDB 329080 — Round 2B

PARTIAL, NOT ACCEPTED. Root decides. No credit claimed.

Closed exactly two original Props: `FiveChordLemma` and `FourChordEnumeration`. The first exhausts all 945 endpoint matchings with kernel certificates and formal enumeration completeness. The second proves exactly four classes at n = 4 under the unchanged literal equivalence closure: positive ranges, pairwise inequivalence, and exhaustive coverage of all 105 matchings.

Additional results prove the n = 3 triangle rigidity case, the complete n = 3 range-{1,2} classification (exactly one class), and a formal negative control refuting uniqueness at n = 4. `ChordComb2Final.lean` supplies the reduced conditional endpoints.

Still unproved here: general `RepresentativeExistence`, `BipartitePlanarity`, `TriangleReduction`, and general `TriangleRigidity`. The n = 3 rigidity case is discharged; `TriangleRigidityLarge` explicitly isolates n ≥ 5. `RepresentativeStep` isolates the unproved inductive range-preservation step, and only the induction assembly from that hypothesis is proved. These auxiliary Prop definitions are not axioms and are not claimed discharged.

The intended endpoint now assumes exactly `RepresentativeExistence`, `Heredity`, `TriangleReduction`, and `TriangleRigidity`; the n = 4 endpoint is unconditional. Model Props are left to lane 2A. No model Prop has been asserted proved by this lane.

All 33 inherited Round 1 Lean sources remain byte-identical. See `hashes/inherited-before-sorted.sha256` and `hashes/inherited-after.sha256`. The source packet was extracted from the required archive with SHA-256 03971d4610581095feddea8040bd178f017d459794ac3e2374e73402d93ccbab.

Validation receipts and exact audit totals are in `VALIDATION.md` and `results.json`. The full declaration audit distinguishes LOCAL declarations from upstream runtime metadata. The bounded failed dihedral build attempts remain in the logs. All execution uses the lane-local capped wrapper; no child agents, git operations, external messages, uploads or browser tabs were used.

Next round: prove the end-edge transfer rule with an end-edge face-state invariant, then use the supplied induction assembly. Prove bipartite planarity by removing an innermost monochromatic chord with the refined face-splitting criterion. Prove shortest induced odd-cycle existence and compression of five retained chords to a `Subdiagram`, using Heredity only as a hypothesis or lane 2A theorem. Finally prove the pair/arc/adjacency argument for n ≥ 5, including transport under the literal equivalence and the triangle-choice consequences of `FiveProperty`.
