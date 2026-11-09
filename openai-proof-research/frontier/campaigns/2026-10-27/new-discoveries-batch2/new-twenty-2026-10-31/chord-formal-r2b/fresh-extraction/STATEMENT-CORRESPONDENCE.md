# Literal correspondence

Primary text: Burns, Jonoska and Saito, “Genus Ranges of Chord Diagrams”, arXiv:1410.6148v1, Conjecture 3.4; cached source `../expanded-corpus-r137/sources/329080.txt`. MathDB 329080 states n is a positive integer and repeats: “For any n ≠ 4, there is a unique (up to equivalence) chord diagram with genus range {1, 2}, and it is (123123)(44⋯nn).”

The frozen definitions and all 33 Round 1 modules are unchanged. `Diagram n` is a fixed-point-free involution on 2n endpoints in backbone order. `Equivalent` remains the equivalence closure of literal rotations and reflections of these endpoint pairings; renaming chord symbols is already suppressed by the involution encoding. `Range12` is pointwise membership equivalence with g = 1 or g = 2. `HasGenus` is exactly 2g + b = n + 2, with b the frozen rotation-system boundary counter. The two empty-circle terms remain in the frozen dart model.

| Target | Lean statement | Scope |
| --- | --- | --- |
| Five-chord obstruction | `Chord.Comb2.fiveChordLemma : Chord.FiveChordLemma` | Exact frozen Prop, not a Boolean-only surrogate |
| Exactly four classes at n = 4 | `Chord.Comb2.fourChordEnumeration : Chord.FourChordEnumeration` | Four positive ranges, pairwise inequivalence under the literal closure, and completeness for every diagram |
| Triangle core at n = 3 | `Chord.Comb2.triangle_three` | Literal equality to r3Block 3 from HasTriangle |
| Intended conjecture | `Chord.Comb2.conj34_intended` | n ≥ 3, n ≠ 4, still conditional on four named Props |
| Printed defect | `Chord.Comb2.conj34_literal_false` | Frozen unconditional exclusions at n = 1 and 2; zero credit |

The frozen `FiveProperty` states an isolated chord plus `HasTriangle D → Equivalent D (r3Block 5 ...)`. This is the exact Round 2B target. It does not itself quantify over every chosen triangle and its arcs. The large-n rigidity proof must still justify the arc consequences it uses from this equivalence statement, including any transport and triangle-choice facts. This packet does not substitute an informal arc claim for the literal Prop.

The model Props (`DartBridge`, `OrbitCounterCorrect`, `FacePermutationCorrect`, `EulerRealization`, `Deletion`, `Heredity`) belong to lane 2A. None is asserted proved by this lane. The new finite certificates evaluate the frozen defining boundary directly. General semantic model correctness remains a separate assembly obligation.
