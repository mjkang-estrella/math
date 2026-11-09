# Statement correspondence

Primary text: Burns, Jonoska and Saito, *Genus Ranges of Chord Diagrams*, arXiv:1410.6148, Conjecture 3.4. The cached source and MathDB 329080 record are read-only in `../expanded-corpus-r137/sources/329080.txt` and `../expanded-corpus-r137/raw/329080.jsonl`.

Literal source: “For any n ≠ 4, there is a unique (up to equivalence) chord diagram with genus range {1, 2}, and it is (123123)(44 ··· nn).” The root ruling restricts the credit-bearing intended assertion to n ≥ 3, n ≠ 4; the printed n=1,2 cases are false and carry no credit.

| Source notion | Unchanged Lean definition | Round 5 status |
| --- | --- | --- |
| Chord diagram / double-occurrence word | `Chord.Diagram n`, a fixed-point-free endpoint pairing in backbone order | Inherited representation suppresses symbol names; the source explicitly identifies the word and pairing pictures. A separate literal word/pairing bijection is not added here. |
| Rotation, reversal, symbol renaming | `Chord.Generator`, `Chord.Equivalent := Relation.EqvGen Generator` | Unchanged literal cyclic/reflection conjugations; names are suppressed. |
| 4^n band-side assignments | `Chord.Sides n := Fin (2*n) → Bool` | Unchanged; both ends choose independently. |
| Boundary components b | `Chord.boundary` | Textbook 6n half-edge rotation-system cycle count, empty annulus count 2. |
| Alternative dart count with unattached-circle terms | `Chord.dartBoundary` and `Chord.emptyCircles` | Unchanged; the general `Chord.DartBridge` is still unproved. This remains a root-ruling fidelity obligation. |
| Lemma 3.1, 2g+b=n+2 | `Chord.HasGenus` | Exact natural-number equation; no division or rounding. General realization remains conditional on BandErasure. |
| Genus range | `Chord.genusRange`; `Chord.Range12` | The set of exact genus witnesses over all assignments, with Range12 specifying exactly 1 and 2. |
| (123123)(44···nn) | `Chord.r3Block` | Unchanged explicit endpoint pairing. |
| Intended Conjecture 3.4 | `Chord.Round5.conj34_intended` in `Chord5Final.lean` | Conditional on the four Props listed in PROOF.md; not an unconditional proof. |
| Exactly four classes at n=4 | `Chord.Round5.conj34_n4` | Unconditional inherited finite classification. |
| Printed small-size defect | `Chord.Round5.conj34_literal_false` | Unconditional inherited universal nonexistence for n=1,2. |
| Odd-cycle graph-window step | `Chord.Round5.oddCycleWindow_proved` | Exact frozen `Chord.Comb4.OddCycleWindow`; does not assume planarity or heredity. |

No source theorem is changed, shadowed or renamed. Existing small sanity certificates and negative controls remain inherited. The graph argument adds no semantic bridge from a different genus or equivalence definition.

The finite rigidity preparation is `Chord.Round5.triangle_endpoints_unique`. It quantifies over arbitrary chosen triangles of an arbitrary five-chord diagram equivalent under the unchanged EqvGen relation to r3Block 5. It is not a replacement definition of equivalence or a global rigidity assumption.
