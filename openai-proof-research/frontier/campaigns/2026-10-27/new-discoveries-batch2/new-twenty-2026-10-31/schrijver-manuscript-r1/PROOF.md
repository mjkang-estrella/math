# Proof and exact scope - DRAFT

For natural k,r with 2 ≤ r and r+2 ≤ k, SchrijverUnitGap asserts that the integer difference of the literal graph diameters at 2k+r and 2k+r+1 belongs to {0,1}. It uses cyclic stable k-subsets with literal disjointness adjacency. Positions are zero-based Fin n in Lean and one-based in the source. Both graphs in the counterexample are proved connected, so Mathlib's disconnected-diameter convention is irrelevant.

Take k=12,r=3. The explicit pair
A={1,3,5,7,9,11,14,16,18,20,23,25},
B={1,3,5,7,10,12,15,17,19,21,23,26}
has masks 21669205 and 39144021. A labelling of all 819 vertices has labels 0 and 8 at these vertices, with the label increasing by at most one on each oriented disjointness edge. Induction on walks bounds every A-to-B walk below by eight. A checked parent tree gives connectivity. Thus D(SG(27,12))≥8.

For SG(28,12), all 3,185 vertices lie in the rotation orbits of 116 certified roots. Each root has a spanning parent tree of depth at most six. Rotation is a literal graph automorphism. Rotate an arbitrary first endpoint to a root, follow that root's tree to the rotated second endpoint, and rotate back. Thus D(SG(28,12))≤6. The difference is at least two and cannot be zero or one. This refutes the universal statement.

The source-only Lean packet proves Schrijver.mathdb_352827 : ¬ SchrijverUnitGap without residual hypotheses. The key bridges are bounded encode/decode inverses, exact reference enumeration, path-generator completeness, kernel-decided filtered-list equality, stored-mask validity and injectivity, adjacency-preserving graph isomorphisms, soundness of label/parent checkers, rotation automorphisms and exhaustive rotation witnesses, and metric transport. See paper §§4–5 and evidence/schrijver-formal-r5/STATEMENT-CORRESPONDENCE.md.

Our ordinary checker independently verifies exact diameters 8,6,9,7 for (27,12),(28,12),(29,13),(30,13). These equalities are stronger than the formal endpoint requires. It also verifies diameter five for SG(14,6), and the disjoint radius-two balls of the explicit correction pair. Theorem 6 is a correction remark only, with no credit claimed, and is not a premise of the r=3 proof.

The r5 and fidelity audit reports are supplied evidence, not a new Lean run here. Root's decisive replay-result.json is absent at manuscript packaging; root replay is pending. No acceptance or priority is claimed. Journal body unread and bounded prior-art limits remain.

The seven-page paper contains the complete ordinary argument and certificate specification. scripts/verify.py regenerates stable vertices, reconstructs literal adjacency, checks exact BFS recurrences and full rotation coverage, and safely extracts and checks the unchanged formal packet. It executes no Lean-related tool.
