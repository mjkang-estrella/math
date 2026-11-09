# Round 2 handoff: MathDB 354228

PARTIAL, NOT ACCEPTED. No credit claimed; root decides. The full even-case conjecture remains unproved.

This round discharges `ModelStructure`, `ModelLeaves` and `LowerBound` as `modelStructure`, `modelLeaves` and `lowerBound`. All seven inherited modules remain byte-identical to the frozen round-1 packet. The source packet hash was checked before extraction.

New proved material:

- An explicit parent map, unique parent, `Fin t` child equivalence and child count.
- The equivalence between nonroot vertices and unordered graph edges, proved injective and surjective.
- Connectedness by induction on depth, and acyclicity using connectedness plus the edge/vertex cardinality criterion; the full structural certificate.
- The exact degree formula, degree one exactly at depth n, and the leaf count t^n.
- Literal weight identities reindexed by incoming endpoints, then split into incoming and child contributions, including the `Fin t` incidence formula.
- The leaf lower bound for every t >= 2 and depth n >= 1, even without using local properness. Distinct leaf weights come from distinct incident edges; an edge with maximum label has a parent with another positive incident edge.
- The explicit depth-one construction for every t >= 2, and the binary depth-two source Figure 5 construction. Both use actual edge equivalences and prove properness and the exact colour count.

`AntimagicFinal2.lean` uses the separate namespace `Antimagic.Round2`, preserving every inherited declaration. Its `even_case` assumes only `RemainingConstruction`. Its `mathdb_354228` assumes only `RemainingConstruction` and `ModelBridge`. `depth_one` is unconditional. The remaining construction Prop explicitly excludes the two closed cases. It requires the exact inherited formula, not merely some labelling.

Still open: depth two with even t >= 4; depth at least three with all even t >= 2 including the binary patch; the arbitrary finite full-tree isomorphism bridge. All six inherited regression parameter pairs now also have literal finite incidence certificates via certified_construction. No general construction claim follows from these finite checks.

Validation details and machine-readable audit totals are in results.json. Replay is serial, bounded, and uses the pinned read-only packages. Local declaration metadata is separated from upstream metadata. Only propext, Classical.choice and Quot.sound occur as axioms in the audited closure. No self-acceptance is asserted.
