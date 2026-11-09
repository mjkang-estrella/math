# Consolidated current correspondence - DRAFT

The endpoint GridFinal6.mathdb_343536 has no proof-obligation premise. All dimensions are natural with 1 <= m,n. GridBasic.G is literally Mathlib pathGraph.boxProd on Fin m x Fin n. IsEquitable is Definition 5.1 via Nat.card of finite neighbour/class subtypes. GridNeighbours.equitable_iff_neighborCells identifies it with multiset equality on Quotient r, with multiplicities. EqPart is the equitable Setoid subtype in relation-inclusion order, finer <= coarser. GridLattice supplies its complete lattice unconditionally; meets are equitable common-refinement joins. Subgroup is of the full graph automorphism group in inclusion order. orbitSetoid uses natural evaluation, and HasFreeVertex uses the full group.

The three endpoint conjuncts match the three source sentences, including abstract order/lattice isomorphism and the exact exceptional formula 2 <= m /\ m = n /\ n <= 3. GridFinal.natural_iso_of_free and natural_iso_iff yield the natural orbit-map strengthening after the three obligations are discharged. Positivity includes singleton/path cases and excludes empty grids.

MainOrbit is proved as Grid343536.main_orbit_proved, OrdinaryBorderTransitivity as ordinary_border_transitivity, FreeClassification as free_classification, and ExceptionalNoIso as exceptional_no_iso. Historical 'unsolved' comments are retained in frozen sources but are superseded by those theorems. The current paper and PROOF.md consolidate the status instead of repeating stale partial headlines.

The ordinary proof's Lemma 8 obtains positive full-group free vertices via MainOrbit; Lean's GridFreeClassification proves the classification independently by side rigidity. The ordinary exceptional cardinality argument uses MainOrbit and ten dihedral subgroup orbit images; Lean uses complete four-point candidate enumeration and ten actual subgroup witnesses independently. These are explained alternative dependency routes, not identical proof scripts.

Source: arXiv:1908.05797 v2, Definition 5.1, Example 5.5, Conjecture 5.6; partition order in Example 2.2, lattice existence Proposition 4.5 / Example 5.3. The journal body was not accessed. MathDB's unrelated 2018 reference is preserved in the raw line, not silently repaired.

Final fidelity verdicts: A-C PASS, D-E QUALIFIED_PASS. All six gate-E editorial requirements are mapped in gate-E-map.json. Root's separate corrected receipt reports 47/47 modules and 4/4 rejected controls. Acceptance remains pending root's paper assessment.
