# Part B remains incomplete; zero credit

The declaration `finite_obstruction : Nut8.FiniteObstruction` is absent. No
unconditional endpoint or self-acceptance is claimed. The interface has not been
shown false, and no mathematical impossibility of the plan has been established.
All inherited Lean source files are unchanged.

## 1. B2 universal coverage: partially advanced

New proved bridges:

- `supportGraph_connected` extracts a connected simple off-diagonal support from
  every `Structural C s`. Its vertices are literally `Fin 8`.
- `supportGraph_degree_le` proves every degree is at most three from the absolute
  row sum, by bounding the number of nonzero entries by their absolute sum.
- `connected_removable_vertex` invokes mathlib's spanning-tree-leaf theorem.
- `deleteFinIso` identifies deletion transported along `finSuccAboveEquiv` with
  the actual induced complement of the removed vertex.
- `connected_subcubic_deleteFin` preserves connectedness and maximum degree three
  on the standard smaller finite vertex type.
- `checkedEquiv` converts a successful permutation-list certificate to a genuine
  permutation of `Fin n`. `graphIsoCheck_equiv` converts adjacency-bit identities
  to an actual graph isomorphism. `extensionClosed_equiv` combines this with
  `extensionClosed_sound`.

Still missing, in dependency order:

1. Define the graph represented by each catalogue code and prove its simple-graph
   adjacency specification. The current conversion accepts graphs with supplied
   adjacency specifications; it does not construct these specifications for all
   catalogue members.
2. Given a deletion isomorphism from the induction hypothesis, extend its labels
   to the new vertex and encode the transported neighbor set as `mask < 2^n`.
3. Prove that mask is eligible: it is nonempty by connectedness, has at most three
   neighbors by the degree bound, and each chosen old vertex has deletion degree
   strictly below three because its original degree includes the removed edge.
4. Prove `extendGraph` has precisely the transported adjacency relation, including
   the row-major sum-of-powers-of-two bit-encoding lemma. This is not implied by
   checked finite closure; it requires a separate encoding proof.
5. Wire these facts into induction for orders one through eight, using the actual
   lists and the inherited per-source closure theorems. Prove the one-vertex base.

The new theorems contain no surrogate assumption asserted as universal coverage.
The generic checker-to-isomorphism theorem explicitly takes its two adjacency
specifications as hypotheses, and the extension theorem takes an eligible mask.

## 2. B4 parent data: not advanced

A decreasing-parent tree for each support, possibly after BFS relabelling, is
still needed, together with transport back to the catalogue labels and the full
matrix normalization theorem. Only inherited `treeSign` algebra is available.
Do not assume a catalogue labelling already has decreasing BFS parents.

## 3. B3 augmentation completeness: not advanced

No Lean enumeration of doubled edges and forced diagonal fills, or proof of its
completeness for arbitrary structural matrices over each support, exists here.

## 4. B5 certificates: inherited partial coverage only

Only the inherited first 32 of 9,172 normalized records, plus inherited pilot
certificates, are included. Pilot coverage can overlap the 32; do not add them.
No new certificate batch is generated. The other 9,140 records and exact image
membership theorem remain missing. No unsigned pretest is used.

## 5. B6 composition: absent

The missing B2 induction, B4 parent normalization, B3 enumeration completeness
and B5 full certificates must feed the inherited refutation transport lemmas.
The desired finite obstruction and unconditional target are not obtained.

Work stayed in B2 according to the required priority order. Successful replay of
this partial packet cannot establish FiniteObstruction and receives zero credit.
