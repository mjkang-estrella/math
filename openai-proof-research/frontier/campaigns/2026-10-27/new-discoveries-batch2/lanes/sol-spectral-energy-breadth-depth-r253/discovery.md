# Exact scope and mathematical work

## Retired spectral target

Elphick–Linz–Wocjan, arXiv:2101.05229v3, §1 p2 and Conjecture 1 p3: G has no isolated vertices, adjacency eigenvalues μ1≥…≥μn, s+=Σ(μi>0)μi². The literal claim is n/(n−√s+)≤ω(G). The primary body contains the triangle-free, weakly perfect and Kneser proofs; these alone did not clear the target.

The live primary followup is https://arxiv.org/pdf/2607.18044v1, first submitted 20 July 2026. Theorem 1.2 is √s+(G)≤(1−1/ω(G))n for every finite simple graph on n≥1 vertices, including isolated vertices. Its final proof also establishes n−√s+≥n/ω>0, so rearrangement is legitimate. Thus it literally covers the campaign source, with no chromatic-perfectness or regularity assumption. This is a public proof, not a new deduction of this lane.

Body comparison: write A=A+−A−, A+A−=0, and M=A+∘A+. Schur positivity gives M doubly nonnegative; total mass 1ᵀM1=s+, while 2Σ_edges√Muv=2Σ_edges|(A+)uv|≥tr(AA+)=s+. Lemma1.4 gives 2Σ_edges√Muv≤(1−1/ω)n√(1ᵀM1). Section3 proves this from a random partition into at most ω blocks and a weighted Cauchy–Schwarz bound. Theorem2.3 proves 1/p(v)+Σ_neighbors1/q(vu)≤n by induction on neighborhoods; the associated positive matrix has unit diagonal and reciprocal-entry products≥1, so Lemma2.2 bounds the sum of reciprocal row sums by1. Both this local induction and its propagation to the spectral inequality were read. No residual classical bridge was identified in the read proof. No exhaustive audit of all cited works is claimed.

Consequently neither requested spectral mechanism is an eligible new discovery route. Independent-set blowups would have adjacency spectrum consisting of the symmetric quotient D^(1/2)AD^(1/2) and Σ_i(w_i−1) additional zero eigenvalues (for integer positive part sizes w_i), with zero eigenvalues of the quotient retained separately. In particular, the public theorem already certifies s+≤4n²/9 for every clique-three blowup. Rational weights cannot rescue this target. This accounting is explanatory and receives no separate credit.

## Replacement: two abnormal edges

Primary: https://arxiv.org/pdf/2104.09241v1, §3 Question1 pp8–9. G is bridgeless cubic; c:E(G)→{1,…,5} is proper (not necessarily surjective). For S(v) the three colors at v, uv is abnormal iff |S(u)∪S(v)|=4; normal iff the union has size3 or5. Hypothesis: |N_G(c)|≤2. Conclusion: existence of some normal five-edge-coloring, with no requirement to preserve c or its Kempe equivalence class. Read Proposition3 proof: remove a hypothetical unique abnormal edge, map remaining normal edges into the Petersen graph, pull back a suitable cycle, and obtain a finite graph with exactly one odd-degree vertex. It excludes defect1 but does not repair defect2. Proposition4 explicitly constructs colorings with every defect count≥2 and so does not itself refute the question.

The target is not replaced by the universal Petersen conjecture. Current primary Putman arXiv:2608.10012v1, Theorem1.1, states a simple connected bridgeless cubic graph with no normal five-edge-coloring; Section4 describes explicit CNFs and DRAT certificates. That public theorem refutes the universal assertion. For the narrower conditional question one must additionally exhibit an at-most-two-defect coloring of a noncolorable graph. No such coloring was located here. The archived UNSAT proofs were not independently replayed. Public theorem statements and printed encoding descriptions are not represented as a local certificate.

### Mechanism A: exact Kempe repair obstruction

Use K3,3 with left vertices0,1,2 and right vertices3,4,5; sorted edge order is (03,04,05,13,14,15,23,24,25). Colors (0,1,2,1,0,3,2,3,4) are proper. Abnormal edges are04 and13. The graph is simple cubic bridgeless and is itself normally colorable by a three-edge-coloring. A Kempe move swaps two colors on one connected component of their edge-induced subgraph.

check_repair.py found this witness. verify_checks.py independently builds vertex components and enumerates the distance layers. No coloring at distances0,1,2 is normal. At distance3 a normal coloring exists; check-receipt.json records an explicit path. Defect counts along that path are2,4,4,0. Thus even on this small graph neither one nor two Kempe moves suffice from the displayed coloring. This is a failed shortcut and an uncredited helper observation, not a resolution. It does not rule out longer repairs or repairs outside the Kempe class. The Petersen sample in repair-results.json has zero two-defect colorings in the enumerated canonical-color traversal; no inference about all cubic graphs follows.

The source parity argument suggests extending the cycle-pullback obstruction to two exceptional edges. With two defects, the pullback can have two degree-one vertices and a path between them, so the handshaking contradiction disappears. A repair must control how that path interacts with the other color components. Merely pairing the odd endpoints leaves their endpoint palettes and the other normal edges unconstrained. This is the precise missing global invariant.

### Mechanism B: exact public-construction adaptation

check_construction.py reconstructs the F four-pole, claw C, L=4F+C and G=3L+C using the printed joins. Its relabeling matches the paper's normalized edge-list SHA256 dc16cc18600cf77c8661b7baf89c7019f265299308541961ff884ea7187b4e8b. It checks 112 vertices,168 distinct nonloop edges, degree3, connectivity and connectivity after deleting each edge. The proper five-coloring diagnostic uses only finite integers and a fixed random seed253; it never computes numerical eigenvalues or treats search failure as proof.

The 120000-proposal capped run performed48089 component swaps and reached19 defects. The exact coloring is retained in construction-results.json and directly checked for properness. Nineteen exceeds two; the mechanism did not reach the source hypothesis. A graph with a certified minimum defect≥3 would also not refute the conditional question. The next decisive calculation would be a boundary-state dynamic program on the printed multipoles recording port colors AND endpoint palettes, with additive internal defects and join defects; a port-color-only table loses the normality condition. No such complete dynamic program or minimum-defect certificate is claimed here.

No full literal proof or refutation emerged. Eligibility HOLD; no PROOF.md, Lean, manuscript, public posting or count change.
