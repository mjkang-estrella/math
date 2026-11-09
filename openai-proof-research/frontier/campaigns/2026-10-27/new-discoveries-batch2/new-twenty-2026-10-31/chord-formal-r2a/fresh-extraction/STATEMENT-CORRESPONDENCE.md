# Source correspondence

The literal MathDB 329080 / source Conjecture 3.4 text is: “For any n ≠ 4, there is a unique (up to equivalence) chord diagram with genus range {1, 2}, and it is (123123)(44⋯nn).” The root ruling restricts the substantive intended theorem to n ≥ 3, n ≠ 4; the literal small-size defect carries zero credit. The primary definitions are Burns, Jonoska and Saito, arXiv:1410.6148v1, Section 2 and Lemma 3.1, cached in ../expanded-corpus-r137/sources/329080.txt.

The inherited definitions remain unchanged: Diagram n is the fixed-point-free endpoint pairing; Sides n is an endpoint-to-Bool assignment; theta flips ribbon edges; rho gives the two cyclic vertex rotations; boundary traces rho after theta and gives 2 at n = 0. HasGenus is the exact equation 2*g + boundary = n + 2. Equivalent is the literal rotation/reflection equivalence closure for the name-free pairing. Range12 is extensional equality of genusRange with {1,2}.

| Frozen obligation | Round 2A theorem | Status |
| --- | --- | --- |
| OrbitCounterCorrect | Chord.Model2.orbitCounterCorrect | Exact statement, unconditional |
| FacePermutationCorrect | Chord.Model2.facePermutationCorrect | Exact statement, unconditional |
| DartBridge | Remaining2A first conjunct | Open, including both empty-circle terms |
| EulerRealization | euler_of_deletion | Exact statement, conditional on Deletion |
| Deletion | Remaining2A second conjunct | Open, exact ±1 boundary equation |
| Heredity | heredity_of_deletion | Exact statement, conditional on Deletion |
| intended Conjecture 3.4 | conj34_intended_model2 | Conditional on Deletion and four combinatorial Props |
| exactly four classes at n = 4 | conj34_n4_model2 | Conditional on FourChordEnumeration |
| literal n = 1, 2 falsity | conj34_literal_false_model2 | Unconditional inherited fact |

The boundary-to-two-dart semantic bridge remains open. The round-1 restrictions on acceptance therefore still apply. No finite regression is represented as a general theorem or a complete Lean classification.
