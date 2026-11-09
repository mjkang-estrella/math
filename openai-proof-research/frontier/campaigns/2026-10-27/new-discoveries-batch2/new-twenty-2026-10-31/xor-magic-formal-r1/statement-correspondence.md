# Statement correspondence

| Source / MathDB requirement | Lean declaration | Scope and status |
| --- | --- | --- |
| Simple connected graph; bijection to (Z/2)^n; zero open sum | XorMagic.OpenMagic | Literal, finite arbitrary vertex type |
| Same, zero closed sum | XorMagic.ClosedMagic | Vertex label plus open sum, literal because graph has no loops |
| d-regular graph | OpenExists / ClosedExists use SimpleGraph.IsRegularOfDegree | Literal |
| Order 2^n | XorMagic.card_of_label | Proved from any label equivalence |
| Integer labels in base data | XorMagic.binaryLabel; each Base*.label_bijective | Kernel-proved bijection with coordinate i given by testBit i |
| Complement neighborhood identity | XorMagic.complement_identity | Proved for every n, assuming total label sum zero |
| Proposition 24 cubic contradiction | XorMagic.cubic_obstruction | Every n; no connectivity assumption needed |
| Closed degree 2^n-4 obstruction | XorMagic.no_closed_twelve | Proved at n = 4 only; sufficient to refute each universal statement |
| Printed conjecture, all n | XorMagic.not_printed_all | Exact negation, witness n = 4 and degree 12 |
| MathDB positive-integer reading | XorMagic.not_printed_positive | Exact negation, witness n = 4 and degree 12 |
| Printed conjecture, all n ≥ 4 | XorMagic.not_printed_ge_four | Exact negation, witness n = 4 and degree 12 |
| Corrected open and closed degree ranges | XorMagic.CorrectedAt | Exact predicate, not a proof of the universal theorem |
| All corrected degrees at order 16 | XorMagic.corrected_at_4 | Proved, 8 concrete graph certificates |
| All corrected degrees at order 32 | XorMagic.corrected_at_5 | Proved, 24 concrete graph certificates |
| F4 affine lifts / holonomy | No declaration | Missing |
| Matching decompositions and persistent distinguished cycles | No declaration | Missing; immutable JSON inputs remain nonformal evidence |
| Interpolation and high-degree complement connectivity | No declaration | Missing |
| Corrected existence for every n ≥ 4 | No declaration | Missing; no qualifying endpoint |

The cached source text is inputs/current.txt (arXiv:2512.19278v1), in particular its abstract / Section 1, Proposition 24 and Conjecture 25. The exact cached MathDB line is inputs/372205.jsonl. Hash identities appear in receipts/. No live source, registry clearance or novelty claim is made by this implementation packet.
