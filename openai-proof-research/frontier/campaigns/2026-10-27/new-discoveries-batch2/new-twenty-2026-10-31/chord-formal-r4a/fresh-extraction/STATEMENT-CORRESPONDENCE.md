# Literal statement correspondence

The source and MathDB text is: “For any n ≠ 4, there is a unique (up to
equivalence) chord diagram with genus range {1, 2}, and it is (123123)(44 ⋯ nn).”
The root ruling restricts the intended theorem to n ≥ 3, n ≠ 4, and requires
separate n = 1, 2 falsity and n = 4 counting statements.

The inherited Diagram, Equivalent, Sides, boundary, HasGenus, genusRange and
r3Block are byte-identical. Endpoints are paired positions on Fin (2*n);
equivalence includes cyclic rotation, reversal and renaming. The defining
boundary is the textbook three-half-edge face count, with exactly two empty
annulus circles at n = 0. HasGenus is 2*g + boundary = n+2, with no division.

The source Lemma 4.2's band-removal fact corresponds to the frozen Deletion
Prop. Round 4A closes only its generic permutation-swap ingredient in full
scope. The swapped permutation is the actual faceEquiv multiplied on the
right by swap of the two actual C darts. bandErasure_zero and bandErasure_one
prove the exact normalization only in those sizes. erased_face_formula
identifies its local edge-flip effect in every size but does not compress the
backbone or establish the general equality of orbit counts.

The final conditional theorem retains a BandErasure hypothesis, in addition
to the inherited combinatorial obligations. The requested removal of all model
hypotheses was not achieved. No altered definition or bundled hypothesis is
used to conceal this. DartBridge is still unproved.
