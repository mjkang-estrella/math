# Round 5 proof record

This is a partial implementation, not acceptance. No credit is claimed. Root decides.

Both required SHA-256 packet hashes were verified before extraction. A lane-local merge script reads only `.lean` members, verifies that all 33 shared filenames have identical bytes, and writes the 138-file union. No inherited declaration or file is modified. The inherited source manifest is `frozen/manifest.json`.

## New mathematical work

`Chord5Graph.lean` proves the exact `Chord.Comb4.OddCycleWindow` obligation. For a non-bipartite diagram, construct the simple crossing graph whose vertices are precisely the lower endpoints. A graph 2-coloring extends to the frozen endpoint coloring by assigning each endpoint its lower endpoint's color. Therefore the crossing graph is not 2-colorable. The pinned mathlib closed-walk criterion supplies an odd closed walk.

Choose an odd closed walk of minimum length. If positions i < j before its final endpoint have the same vertex, the subwalk from i to j and its complementary closed walk both have smaller length. Their lengths sum to the odd original length, so one is odd, contradicting minimality. Hence every vertex before the closing step is distinct. A simple graph has no length-one closed walk. The odd length is therefore 3 or at least 5. Length 3 supplies the three literal crossing relations of HasTriangle. Otherwise its first five vertices form the exact injective crossing window. No inducedness assertion is used or required.

`triangleReduction_of_split` combines this theorem with the inherited five-chord path obstruction and the planarity induction, leaving only MonochromaticSplit as its hypothesis. This closes the graph-window step, not unconditional TriangleReduction or BipartitePlanarity.

`Chord5ErasureSetup.lean` proves that a single-chord Subdiagram's endpoint image is exactly the complement of a paired pair. The proof uses injectivity and equal finite cardinalities. The swap of C successors is identical at either omitted endpoint; hence BandErasure is equivalent to the same face-count formula at every omitted endpoint. These lemmas remove choice bookkeeping only. They do not prove the suppression identity.

## Remaining obligations

The intended endpoint remains conditional on exactly:

1. `Chord.Model3.BandErasure` — general face-orbit normalization after removing a band and suppressing its endpoints.
2. `Chord.Comb4.EndEdgeSurgery` — boundary and end-face connectivity identities for appending an adjacent pair.
3. `Chord.Comb4.MonochromaticSplit` — the refined +1 identity for deleting an innermost monochromatic chord.
4. `Chord.Comb4.TriangleRigiditySix` — the pair, common arc, adjacency and literal cyclic equivalence argument for n ≥ 6.

No unconditional Deletion, EulerRealization, Heredity, RepresentativeExistence, BipartitePlanarity, TriangleReduction or full TriangleRigidity is claimed. The previously inherited n=4 classification and n=1,2 literal refutation are unconditional after merging the branches. DartBridge also remains open as the statement-correspondence bridge required by the root ruling, although it is not an assumption of the assembled endpoint using the 6n definition.

Next round should first use omitted_pair with the inherited erased_face_formula and orbitCount_of_retraction to finish backbone compression. Then establish the refined cycle split/merge connectivity test needed by both EndEdgeSurgery and MonochromaticSplit. The arbitrary-n rigidity proof still needs transport of the unique triangle of the five-chord representative through EqvGen and the common-arc/adjacency argument. Finite checks are not replacements for these proofs.

`Chord5EndFace.lean` additionally proves a full-fuel raw-permutation trace membership iff SameCycle theorem from the certified trace origin and saturation lemmas. It specializes this to the frozen EndSame predicate and the actual faceEquiv, using bounded trace congruence. This bridge is unconditional and checked, but it does not assert the end-edge insertion identities.
