# Exact mechanisms and remaining gaps

No new theorem is claimed. All computational statements below describe diagnostics. The source statements, version snapshots, and immutable HTTP receipt hashes are in extracted.json and http/. There is no Lean endpoint.

## 374492: trees and maximal matching moments

Read the source's Conjecture 1.1 and its surrounding extremal definitions. The competing tree has one long branch of length d−1 and n−d branches of length 1, so it has n vertices and diameter d. The objective is uniform average over **maximal**, not maximum, matchings. The 2025 follow-up (Discrete Applied Mathematics 377, 518–528, DOI 10.1016/j.dam.2025.08.016) reports the cases d=6,7,8; the sweep therefore includes genuinely unproved diameter regimes d≥9, without claiming novelty for checking them. That follow-up body remains unread: no candidate could receive novelty clearance on this basis.

Implemented an integer moment dynamic program. Each subtree stores a pair (count, sum of sizes) in three states: its root is unmatched and awaits a parent match; its root is unmatched with all children matched; or its root is matched to a child. Products of moment pairs use (c,s)(d,t)=(cd,sd+ct). Matching an edge adds its count to its size sum. For a maximal matching, the unmatched vertices must be independent, which is exactly the reason for the child-state restrictions. The root accepts only the latter two states. Ratios are compared by cross multiplication, including the conjectured uniqueness clause.

Generated unlabeled trees by adjoining a leaf and deduplicating by the minimum rooted parenthesis code over all possible roots. All trees through order 17 completed, with known count 48629 at order 17; order 18 was interrupted by the 120 second CPU cap before producing a completed row. The table includes all diameters allowed by the conjecture. The independent validation script enumerates all edge subsets for all unlabeled trees through order 9 and agrees with the dynamic program's integer counts and sums.

No counterexample. A full proof would need a diameter-preserving structural transformation that strictly reduces the ratio unless the tree is the stipulated broom. Local inequalities on counts alone are insufficient: both numerator and denominator change, and branching can raise the maximal-matching count without a uniform sign for the ratio. No such transformation has been proved here.

## 375027: spar tableau containment

Read Section 2.1 including the labeling order and Figure 2's numerical example. Implemented literal bottom-to-top, right-to-left greedy labels, excluding the entire immediately-right column and exceeding both neighboring labels. Recovered ord by its odd-column parity prescription and successive column increments. The Figure 2 partition (4,2,2,1) gives ord=(7,4,2,1), i.e. column lengths (4,3,2,2,1,1,1).

All integer partitions of sizes 1 through 42 completed. A second search sampled 30000 partitions with seed 218, height and width below 100, reaching size 5476. For each partition, directly compared all columns of ord before and after deleting the last row. No counterexample.

Potential proof mechanism: propagate an invariant on the two adjacent column-label sets through the greedy algorithm. The missing lemma must control the **cumulative parity changes** in label membership, not just pointwise sizes of label sets. Deleting a row can change forbidden labels in earlier columns; ordinary monotonicity of the mex function does not imply the required partition containment. No invariant sufficient for arbitrary height/width is established. A finite sample does not prove an eventual or uniform claim.

## 374340: majority C-coloring

Read the source's definition, Proposition 3, examples of nonmonotonic edge deletion, Section 7.2, Proposition 21 and Conjecture 1. A color class S is feasible exactly when every v in S has at least ceil(deg(v)/2) neighbors in S. The maximum number of classes is computed by subset-partition dynamic programming, taking the class containing the least remaining vertex. For every edge deletion, recompute degrees and the optimum; check criticality for **every** edge before comparing increasing and decreasing deletions.

All labeled graphs on 2–6 vertices and all 1044 unlabeled graphs on 7 vertices completed. A further 1000 samples each at n=8,9,10 used seed 218 and mixed edge densities. No mixed critical witness. Samples are not exhaustive and can repeat isomorphism classes.

One possible proof strategy is to start with an optimum coloring and use a decreasing deletion to force its endpoints into one class in every optimum. Proposition 21 guarantees an edge with a nondecreasing deletion, but does not force an unchanged deletion. The missing step is an exchange argument producing an unchanged edge whenever any edge decreases the optimum. This has not been proved. The source's examples already show generic nonmonotonicity; merely combining them by disjoint union or a small gluing would be ineligible and was not offered as a candidate.

## Other finite checks

* 374894: computed c(uv) as the maximum clique order containing the edge. Used repeated signless-Laplacian multiplication and the Rayleigh quotient as a **floating-point falsifier**, not a certified spectral upper bound. Checked connected labeled graphs through order 6 and a larger seeded random pass. No exact witness was obtained. The source's signed complete-graph example is a different statement and was not repackaged.
* 374103: applied the exact finite gamma formula in Proposition 5.3. Enumerated all 1023 nonempty 3-uniform hypergraphs on five labeled vertices; 268 satisfy one of the target parameter regimes. Sampled 20000 six-vertex triple systems, with 6350 eligible systems of sparseness 2. Compared rational values by Fraction. No violation. The later cases are sampled, not exhaustive.
* 374204: all seven-vertex atlas graphs were tested for a split partition, vertex connectivity, induced K1,r exclusion, and Hamiltonicity by permutation enumeration. Only qualifying (G,r) pairs are counted. No counterexample. The source handles r=3,4; sampled finite success cannot establish arbitrary r.
* 374904: exact connectivity and removable matching search through order 7. Most small cases are covered by the source. This is a sanity check, not a contribution. No claim is made outside the recorded (graph,k) pairs.
* 374250: direct memoized SG evaluation of legal moves (adding an X without creating XXX) for nonregular single-piece interior boards through total board length 22. The characteristic function was corrected against equation (2.1); the first log used an incorrect residue table and is explicitly superseded by games-corrected.log. No surviving violation. Boundary/paraphrase exceptions are not discovery candidates.
* 374386: all binary words through length 20 satisfying the literal shared-k effective-partition hypothesis were checked, modulo complement symmetry. Distinct abelian-square **factors** were counted, not occurrences or Parikh-equivalence classes. No violation. Do not silently change the source's bound on the small components i,j into a different stronger conjecture.

## Screening limits

No candidate survived to the stage of a full ordinary proof. Consequently there is no claimed printed-obstruction clearance, complete citation-neighborhood audit, or formalization. Printed example/table occurrences for the active sources are indexed in logs/printed-inventory.json, not claimed to be an independent visual classification of every cited figure. Searches of current GitHub trees and Lean Pool are bounded screens, not proof of absence. The OpenAI and Omega root recursive trees were truncated; the relevant preprints, D5 and Library subtree requests were subsequently complete. Lean Pool's retrieved tree was complete. OpenAlex returned 429 on the third query; all subsequent calls in that process were skipped and no retry was made. No source access limitation was treated as a novelty pass.
