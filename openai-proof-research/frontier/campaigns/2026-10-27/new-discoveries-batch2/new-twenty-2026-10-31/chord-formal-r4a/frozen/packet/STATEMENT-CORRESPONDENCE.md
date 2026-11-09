# Source correspondence

The literal source and MathDB text is: “For any n ≠ 4, there is a unique (up to
equivalence) chord diagram with genus range {1, 2}, and it is (123123)(44 ⋯ nn).”
The intended scope is n ≥ 3, n ≠ 4, per the root ruling. The frozen literal
small-size refutation and the exceptional four-chord endpoint are retained.

Frozen `Diagram`, `Equivalent`, `Sides`, `boundary`, `HasGenus`, `genusRange`,
and `r3Block` are unchanged. The boundary is the three-half-edge rotation-system
face count, with boundary 2 at zero chords. Genus is the exact equation
2*g + boundary = n+2, without truncated division.

The source's Lemma 4.2 says removing a band increases or decreases the number
of boundary components by exactly one. This is precisely frozen `Deletion`.
`deletion_zero` and `deletion_one` prove only its instances n=0 and n=1;
`deletion_of_surgery` proves it only from two explicitly unproved Props.
No full-scope deletion theorem is claimed.

New `orbitCount` is the mathematical orbit quotient of a finite permutation.
It includes fixed points. `boundary_eq_orbitCount` bridges it to the literal
frozen boundary at positive n. `BandErasure` describes the actual C-half-edge
successor swap and restricted side assignment; its computational regression
is evidence only, not a proof. DartBridge is still unproved.

No new equivalence, genus definition, representative, or combinatorial endpoint
has been substituted for the inherited objects. The final endpoint's remaining
hypotheses are documented in SUMMARY.md.
