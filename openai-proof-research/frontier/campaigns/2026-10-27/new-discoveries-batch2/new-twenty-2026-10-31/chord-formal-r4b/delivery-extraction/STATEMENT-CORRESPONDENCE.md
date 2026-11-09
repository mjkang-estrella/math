# Statement correspondence

MathDB 329080 and source Conjecture 3.4 say: “For any n ≠ 4, there is a unique (up to equivalence) chord diagram with genus range {1, 2}, and it is (123123)(44 ⋯ nn).” The root ruling restricts the substantive target to n≥3, n≠4 and separately records the printed failure at n=1,2. This round changes no definition of the statement.

| Source notion | Frozen Lean definition and new use |
|---|---|
| Double-occurrence word, with cyclic permutations, reversal and symbol renaming (source §2) | Diagram n is the name-free fixed-point-free involution; Generator and Equivalent give literal cyclic rotation/reflection and their equivalence closure. Unchanged. |
| 4^n attachment choices to inner/outer circles (§2) | Sides n = Fin (2*n) → Bool. appendSides adds the two Boolean choices; oldSides restricts them. |
| End edge traced by one or two boundary curves (§2, Figure 2) | EndSame uses reachability between P_0 and N_(2n−1) in the defining 6n face traversal. General orbit-count correctness remains a model obligation; no topological theorem is claimed. |
| Boundary components and Euler equation (Lemma 3.1) | boundary is the frozen 6n rotation-system count, with boundary=2 at n=0. HasGenus is exactly 2*g+b=n+2. EndInvariant and both surgery obligations refer to this exact boundary. |
| Genus range (Definition 2.1) | genusRange and Range12 unchanged. existence_of_surgery is conditional on EndEdgeSurgery. |
| Subdiagram, induced interlacement graph | Subdiagram is the frozen increasing pairing-closed embedding. compress constructs it from a closed endpoint set; crosses_iff proves exact transport. fiveSelection compresses arbitrary five retained chords. |
| Bipartite crossing graph | Frozen Bipartite assigns Boolean colors consistently at both ends. innermost_monochromatic proves the selection argument. planarity_of_split requires the unproved refined boundary identity MonochromaticSplit. |
| Shortest odd cycle argument (candidate proof, not source theorem) | OddCycleWindow remains an unproved Prop; no shortest induced odd-cycle theorem is asserted. no_five_path proves that its five-vertex alternative contradicts FiveProperty after literal compression. |
| Representative (123123)(44⋯nn) | Frozen r3Block and representative_spec unchanged. Rigidity at n=5 is supplied via the identity Subdiagram; TriangleRigiditySix remains unproved. |
| Main intended scope | Chord.Comb4.conj34_intended is explicitly conditional; conj34_intended_surgery exposes the finer outstanding obligations. |
| Exceptional and printed small cases | conj34_n4 and conj34_literal_false reuse the unconditional frozen certificates. |

Read-only source inputs: chord-root-ruling-r1.json; chord-review-r1/REVIEW.md, review.json and scripts/chordrev.py; expanded-corpus-r137/outputs/329080-proof.md, lean/329080 drafts and PLAN.md, relevant scripts and sources/329080.txt; round-2B SUMMARY.md, PROOF.md, results.json and Lean sources. No new prior-art or novelty claim is made in this implementation round.
