# Proof and remaining obligation

`sameCycle_map` transports a permutation orbit along any map sending successor
steps to orbit steps. Its proof uses natural powers on the finite source.

For a permutation f on Option α with f none = some t, `removeNone f` skips none.
Embedding α by some preserves orbit steps, and the projection sending none to t
preserves orbit steps in reverse. Every ambient orbit meets some α. The inherited
section theorem therefore proves `orbitCount_removeNone`. For a fixed none,
the quotient is equivalent to Option of the remaining orbit quotient. Its
cardinality gives `orbitCount_optionCongr`, without a nonempty-type assumption.

Write f = swap none (f none) * h.optionCongr. After right multiplication by
swap none (some b), three cases suffice. If f none = none, the count decreases
by one. If f none = some (h b), it increases by one. Otherwise suppress none
in both permutations: the smaller permutations differ by the transposition
of h.symm a and b. Induction on Fin size and conjugation by finSuccEquiv' prove
`swapCycleLaw_proved : Chord.Model3.SwapCycleLaw` for every size.

`bandErasure_zero` and `bandErasure_one` check the exact restricted-assignment
normalization, using the inherited classifiers and kernel reduction over all
small side vectors and increasing closed position embeddings. These are not
proofs of general BandErasure. `erased_face_formula` proves for arbitrary n
that the C-successor swap makes theta fix the two deleted C darts and leaves
its other values alone. Rotation rho is still the frozen vertex rotation.

The remaining literal Prop is unchanged:

    Chord.Model3.BandErasure

It quantifies over every single-chord Subdiagram A D and every ambient side
assignment, and asserts that some omitted endpoint p has the swapped face
orbit count equal to boundary A on the actual restricted assignment. There
is no axiom or placeholder implementing it. The generic local-to-global tool
`orbitCount_of_retraction` now permits proving normalization by giving the
retained-dart embedding, a retraction, local orbit steps in both directions,
and a path from each ambient dart to its projected retained dart.

Next work: for positive retained size, construct this retraction by following
the backbone through the two omitted vertices. Prove that the increasing
position embedding takes consecutive retained endpoints to the first surviving
backbone endpoints. Instantiate the retraction theorem on the erased face map.
Treat the empty retained diagram with bandErasure_zero. Then apply the already
proved deletion_of_bandErasure, euler_of_bandErasure and heredity_of_bandErasure.
The general contraction and cyclic-order arithmetic are NOT claimed proved.
