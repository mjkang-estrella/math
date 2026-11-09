# MathDB 343536 — grid-formal-r1

PARTIAL CONDITIONAL FORMALIZATION. No acceptance or discovery credit is claimed.
Root decides. The conjecture is not yet formally proved.

Five mathematical modules compile without placeholders. GridFinal.mathdb_343536
is the literal conjunction of S1, S2 and S3 for all m,n≥1, conditional on exactly:

1. MainOrbit: every equitable partition equals the orbit partition of its A0
   colour-preserving subgroup, including paths, ladders and square grids.
2. FreeClassification: a full-Aut free vertex exists iff the grid is not 2×2 or 3×3.
3. ExceptionalNoIso: for k=2 or 3, EqPart(G k k) and Subgroup(Aut(G k k))
   admit no abstract order isomorphism.

These are Lean Prop definitions, not new axioms. Their exact quantifiers are in
src/GridFinal.lean. No hidden source theorem is assumed.

Completed: literal Mathlib box-product graph; Definition 5.1; source refinement order;
full automorphism subgroup orbits; orbit equitability; order preservation; reflection
of order at a free vertex; natural order isomorphism conditional on surjectivity;
explicit row/column reflections and transpose; corrected A0 and Hpi;
no-free proofs for both exceptional squares; kernel-decided 7- and 9-labeling
regression tables with a proved Definition 5.1 bridge; negative controls.
No enumeration of all large-grid partitions is used.

Limitations: the tables give distinct equitable labelings, not exhaustive counts,
and do not establish the ten-subgroup counts. The general EqPart lattice instance
is not supplied. The endpoint currently uses the inherited source-ordered poset;
an order isomorphism between lattices preserves the lattice operations.

Next round: prove positive-layer propagation (the old skeleton omitted positivity),
multiset neighbour determinism, non-backtracking side walks and corner timing,
conjugation under WLOG isomorphisms, border transitivity, paths and ladders.
Then discharge MainOrbit; establish positive free vertices via Corollary B; prove
the two finite subgroup collisions and finiteness obstruction; build the equitable
partition lattice. Reuse the completed generic orbit/order results.

The updated PROOF.md explicitly repairs all three reviewed presentational gaps.
STATEMENT-CORRESPONDENCE.md records source semantics and the remaining infrastructure.

Replay instructions are in REPRODUCE.md; detailed machine results are in results.json
and verification/replay-report.json. Historical failed experiments remain in logs.
The delivery is grid-formal-r1-source.zip, freshly extracted into verification/.
All artifacts and logs remain in this lane; no git, shared ledger edits, network,
browser, upload, external messaging, or child agents were used.
