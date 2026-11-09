# Statement correspondence

MathDB 329080 and Conjecture 3.4 of Burns, Jonoska and Saito, Genus Ranges of Chord Diagrams, state: “For any n ≠ 4, there is a unique (up to equivalence) chord diagram with genus range {1, 2}, and it is (123123)(44 ⋯ nn).”

The intended endpoint uses n ≥ 3 and n ≠ 4, following the root ruling; the source's table itself rules out n = 1,2. The endpoint explicitly records that literal defect and the exactly-four n=4 classification.

All mathematical definitions are inherited byte-identically. Diagram n is a fixed-point-free involution on cyclically ordered Fin (2*n), suppressing letter names. Equivalent is the equivalence closure of rotations and reflections conjugating the partner involution; renaming is implicit in the name-free encoding. Sides n assigns one Bool independently to each endpoint. Boundary is the textbook face-permutation cycle count on the 6*n half-edges, with boundary 2 at n=0. HasGenus uses 2*g + boundary = n+2. Range12 is the literal membership equivalence g=1 or g=2. The representative pairing is the triangle followed by adjacent pairs.

Root's chord-root-clarification-r2.json says DartBridge is NOT required because every endpoint and proof uses boundary, not dartBoundary. This round follows that clarification.

New theorem correspondence: successor swaps split one face cycle or merge two, with the exact SameCycle criterion. The innermost closed face proves the precise +1 equation needed by the inherited planarity induction, conditional on BandErasure's normalization identity. Neither theorem is claimed to replace the missing normalization proof.

Chord.Round6.conj34_intended is CONDITIONAL on BandErasure, EndEdgeSurgery and TriangleRigiditySix. Chord.Round6.conj34_n4 and Chord.Round6.conj34_literal_false are unconditional. No inherited declaration was edited, renamed, or shadowed.
