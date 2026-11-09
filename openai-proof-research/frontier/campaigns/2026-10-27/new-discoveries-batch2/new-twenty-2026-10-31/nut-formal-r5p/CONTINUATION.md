# Concrete continuation for root or the next assigned worker

This is a plan, not a checked proof. Keep all inherited modules unchanged.

The main remaining geometric lemma is strict deletion degree at a chosen
neighbour. For G on Fin (n+1), deleted v, old i, let
S = ((deleteFin G v).neighborFinset i).image v.succAbove.
Use succAbove injectivity to identify |S| with the deletion degree.
The image is contained in G.neighborFinset (v.succAbove i). If that old vertex
is adjacent to v, then v belongs to the latter but not to S. Thus the inclusion
is strict, and Finset.card_lt_card yields deletion degree < original degree.
Combine with the subcubic bound to obtain deletion degree < 3.

For mask cardinality, the chosen old vertices map injectively to the full
neighbour set of v via i ↦ v.succAbove (e i). Every neighbour of v is unequal
to v by looplessness, so finSuccAboveEquiv v and e.symm give the inverse.
Translate the List.range-filter length in eligibleNeighbors to this finite set
cardinality. The identity transportedMask_bit is already available, and
transportedMask_lt supplies the required List.range (2^n) membership.
Connectedness on Fin (n+1), with n > 0, supplies a neighbour of v; this proves
nonemptiness. The original degree bound supplies at most three neighbours.
The deletion adjacency specification identifies graphDegree with deletion degree.

Build a membership-indexed closure lemma for each actual old catalogue list:
∀ a ∈ oldTargets, ∃ cs, extensionClosed n a newTargets cs = true.
Use the inherited closed0, closed1, ... theorems directly; membership case splits
can be generated from the same source lists. This avoids rechecking certificates.
Some per-source certificates live in subsequent GraphClosureN_00k modules.
The targets definitions in these chunks have identical values but distinct names;
explicit rfl conversions can identify them with GraphClosureN_000.targets.

Inductively obtain an actual graph isomorphism from the old catalogue graph
into deleteFin G v. Its underlying permutation gives e in extendLabels.
Use catalogueGraph_adj, the old isomorphism's map_rel_iff, and
transported_extension_spec for the graph comap along extendLabels v e.
The missing eligibility lemma then unlocks extensionClosed_equiv. Compose its
resulting isomorphism with the comap isomorphism induced by extendLabels.
At order eight, the resulting map sends catalogue labels to supportGraph
labels, which is exactly the direction required by C.submatrix e e.

FinalEndpoint.lean deliberately imports the missing Coverage8 module. Once
Coverage8.lean genuinely proves Nut8.coverage8, include it in modules.json in
dependency order and rerun a new extracted source-only packet. Also include
FinalEndpoint in AuditAll's module allowlist; the current conditional driver
checks it with Lean and leanchecker but the current AuditAll cannot audit a
future file it does not yet import. MissingCoverage negative control must then
be replaced by an intentionally invalid coverage claim, since the declaration
will exist. Do not reuse the current partial replay as full-endpoint validation.
