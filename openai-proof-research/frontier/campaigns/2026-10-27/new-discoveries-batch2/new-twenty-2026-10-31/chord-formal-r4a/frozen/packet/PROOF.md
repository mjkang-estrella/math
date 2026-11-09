# Proofs and exact remaining obligations

`ChordModel3Orbits` constructs the least member of a SameCycle class in Fin size.
The subtype of these minima maps injectively to the orbit quotient: two minima
in the same class are bounded above by each other. Every class has a minimum,
so this map is bijective. Round 2A's bounded minimum theorem and certified scan
then identify the frozen evaluator with Nat.card of the quotient. A bounded
extensionality lemma for trace and cycles transfers this equality to faceEquiv.
The empty diagram remains separate, with boundary exactly 2.

`ChordModel3Transport` uses quotient congruence to prove invariance under orbit
correspondence. Inversion uses sameCycle_inv; conjugation uses sameCycle_conj.
Intertwining permutations intertwines their natural powers, so it reflects and
preserves SameCycle. The section theorem constructs a quotient map, proves
injectivity by reflection of SameCycle, and surjectivity by the orbit-meeting
hypothesis. It does not construct a first-return permutation.

`ChordModel3Base` proves the last-band deletion from the existing one-chord
boundary values. For two chords it exhausts the three possible pairings using
the inherited classifier. Each pairing has a kernel-decided lemma over all
order embeddings Fin 2 -> Fin 4 that commute with pairing, and all side vectors.
Thus it checks the restriction correlation, not merely the possible boundary
values separately.

## Remaining statements (literal Lean Prop definitions)

`Chord.Model3.SwapCycleLaw`: for any permutation f of Fin size and distinct a,b,
`orbitCount (f * swap a b)` is `orbitCount f + 1` or is one less than
`orbitCount f`. No proof is present.

`Chord.Model3.BandErasure`: given any actual single-chord Subdiagram A D and
assignment c, there is an omitted endpoint p such that the orbit count of
`faceEquiv D c * swap (chordDart p) (chordDart (D.partner p))` equals the
boundary of A with its restricted assignment. No proof is present. This is a
normalization on the three-half-edge face permutation; it must include the
empty annulus, where the count on the left is 2.

`deletion_of_surgery` substitutes these two equations. The two C darts are
distinct by injectivity of chordDart and the frozen noFixed field. The positive
ambient diagram's orbit count equals its boundary. This gives precisely the
frozen Deletion disjunction. `consequences_of_surgery` applies the frozen
round-2A reductions without modifying them.

## Next-round plan

1. Prove SwapCycleLaw, preferably with the refined split/merge SameCycle test.
2. For BandErasure, swap the two C successors, suppress the two now bivalent
   vertices, and use orbitCount_of_section to transport to retained half-edges.
   When no retained vertex exists, handle the two annulus orbits directly.
3. Define deletion_proved from deletion_of_surgery, then apply the unchanged
   euler_of_deletion and heredity_of_deletion. Remove Deletion from the final
   conditional endpoint only after this succeeds.

Neither generic surgery obligation has been replaced by an axiom, opaque
assumption, or assertion of computational evidence as proof.
