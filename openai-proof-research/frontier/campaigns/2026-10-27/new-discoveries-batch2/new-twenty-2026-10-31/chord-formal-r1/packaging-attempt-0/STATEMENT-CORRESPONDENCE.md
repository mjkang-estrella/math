# Source correspondence

Source: Burns, Jonoska and Saito, “Genus Ranges of Chord Diagrams”, arXiv:1410.6148v1, Conjecture 3.4. Cached primary text read from ../expanded-corpus-r137/sources/329080.txt; root ruling ../chord-root-ruling-r1.json; review ../chord-review-r1/REVIEW.md.

Literal conjecture reproduced by MathDB 329080: “For any n ≠ 4, there is a unique (up to equivalence) chord diagram with genus range {1, 2}, and it is (123123)(44⋯nn).” MathDB additionally says n is a positive integer. The source table contradicts the literal quantifier at n = 1 and n = 2. These defects are proved without hypotheses by conj34_literal_false and printed_conjecture_false, and carry no credit.

| Source notion | Lean encoding | Status |
| --- | --- | --- |
| n-chord diagram | Diagram n: fixed-point-free involution on Fin (2*n) | Implemented; allowed encoding in TASK.txt |
| rotation, reversal, renaming | Generator conjugates the endpoint involution by a literal cyclic shift or reflection; Equivalent is its equivalence closure | Literal setoid implemented; word/involution quotient correspondence not yet proved |
| in/out choices, 4^n | Sides n = Fin (2*n) → Bool | Literal choices; exponent cardinality theorem not supplied |
| rotation-system boundary count | theta exchanges backbone/chord half-edges, rho cycles P,N,C, face = rho ∘ theta, cycles traverses faces | Computable; generic orbit-count certification still open |
| two-dart model | dartBoundary, nextSame, emptyCircles | Implemented; generic DartBridge open |
| two empty circles | emptyCircles contributes two at n = 0; boundary gives 2 for the empty diagram | Kernel sanity facts supplied |
| Euler genus | HasGenus D c g iff 2*g + boundary D c = n+2 | Exact natural-number equation, without division; global existence open |
| genus range | genusRange D = {g : Nat | ∃ c, HasGenus D c g} | Implemented |
| {1,2} | Range12: membership iff g=1 or g=2 | Literal extensional set equality |
| (123123)(44⋯nn) | r3Block, with explicit blockMate pairing | Uniform pairing validity and specification proved |
| intended n ≥ 3, n ≠ 4 uniqueness | conj34_intended | CONDITIONAL, five outstanding mathematical Props |
| exactly four classes at n = 4 | ExactlyClasses 4 4, conj34_n4 | CONDITIONAL on exact enumeration obligation |

The root's four definition conditions have NOT all been discharged. Empty-circle terms and the exact genus equation are implemented; generic rotation-to-dart correctness, exhaustive class-count sanity proofs and formal enumeration completeness remain unfinished. No literal full-scope resolution is claimed.
