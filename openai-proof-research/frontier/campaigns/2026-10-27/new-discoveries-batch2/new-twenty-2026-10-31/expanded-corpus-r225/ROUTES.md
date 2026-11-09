# Mathematical routes and exclusions

These arguments and diagnostics are not submitted as significant new solutions.

## 362341: a routine subdivision obstruction

Let H be the Mycielski graph of K9: old vertices v1,...,v9 form a clique; independent twin vertices u1,...,u9 satisfy ui~vj exactly when i differs from j; the apex w is adjacent to all ui and to no vi. H has 19 vertices and 117 edges. It has no K10: a clique contains at most one twin, and if it contains w it has size at most two; without w it has at most nine vertices. H is not 9-colorable. The old clique would occupy all nine colors, and if w has the color of vi, its twin ui can have neither that color nor the colors of any of the eight other old vertices. This is the classical Mycielski argument.

Subdivide every edge of H exactly once to get S(H). Its edges partition into two star forests: orient each edge of H by an arbitrary total ordering, put the half incident with the tail in the first layer, and the other half in the second. Therefore S(H) is biplanar. In every odd coloring in the SOURCE sense (some neighborhood color occurs oddly), the two neighbors of every degree-two subdivision vertex must have different colors. Restricting to old vertices gives a proper coloring of H. Thus chi_o(S(H)) is at least ten.

S(H) has no K10* subgraph. A branch vertex of a K10* has degree nine, so cannot be a subdivision vertex. Every length-two path between old vertices of S(H) corresponds to an edge of H; hence such a subgraph would induce a K10 in H, impossible. This refutes the printed n=9 assertion. It combines exactly the source's subdivision forcing with the classical Mycielski construction, and is rejected as a routine/source-ingredient route under the user's rules. It is not a candidate. The source's claim that K_n* has girth four is also a convention/typo issue (for n>=3 its girth is six), not a discovery.

## 362571: excluded smallest-parameter correction

Definition-level enumeration of all 120 permutations of five letters gives

P5(t)=1+11t+36t²+11t³+t⁴,
Q5(t)=15t+30t²+15t³=15t(t+1)².

For nonzero real t,

P5(t)/t²=(t+1/t+11/2)²+15/4 > 0,

and P5(0)=1. Thus P5 has no real zero and is not real-rooted. The source already gives P-Q=(1-t)^(n-1), from which the same polynomial is immediate. Shankar's slides state the intended range n>5. This is expressly a zero-credit source-formula and smallest-parameter correction. The author attribution to Fulman–Kim–Lee–Petersen in the MathDB title does not change that. The intended n>5 problem is not proved here.

## 362623: excluded by current source remark

The profile (2,2,2,10,16) has sum 32, all entries positive even, and maximum 16. Projecting any Hamilton cycle of Q5 onto its first three coordinates gives a closed walk visiting every one of the eight projected vertices. It must use at least eight projected edges, but this proposed profile has only six. Current v3 Remark 3.3 states exactly this missing subset condition and cites older work. The direct counterexample is therefore not new and not eligible.

## 362708: low-dimension route and classical bridge risk

For immersion order, the coefficient at weight (1^n) is f^lambda, the number of standard tableaux. Hence lambda <=_I (n-2,2) implies f^lambda <= n(n-3)/2. The source's Remark 3.41 already proposes precisely this test and supplies all four desired inclusions.

The hook-length scan checked every partition at n=5 and 9 through 45. The only shapes under that dimension threshold were (n), (n-1,1), (n-2,2) and their conjugates. The first two are excluded by dominance (their content equal to their own shape has positive Kostka coefficient, whereas the target has zero). The remaining four shapes give the conjectured interval. However this is finite diagnostic coverage, not a uniform proof. Rasala's classical minimal-degree classification appears to supply the intended uniform exclusion. The 2015 primary follow-up, Lemma 3.1, quotes the consecutive distinct minimal degrees n-1, n(n-3)/2, (n-1)(n-2)/2 for n>=9; it does not by itself provide a complete checked equality-SHAPE classification in the inspected passage. No novelty credit is claimed, even conditionally. The elementary bridge and source's explicit strategy make this unattractive for further Lean investment.

## 362437: literal finite weak-graph checker

A vertex v is nonredundant exactly when two neighbors x,y are nonadjacent and have v as their unique common neighbor. The scripts implement this local two-walk test directly. They do not rely on the source's chordless-cycle characterization. Every vertex must be nonredundant. Disconnected graphs are allowed; no isolated vertices pass.

For each sampled weak graph, candidates minimize (number of degree-two neighbors, degree) lexicographically. A minimum-cardinality set of missing neighbor-neighbor edges covers all degree deficits caused by deleting the selected vertex. Minimum fills are enumerated. The resulting graph is then checked for a weak spanning subgraph by exact edge-deletion recursion, preserving minimum degree two. Successful cases have explicit finite witness existence established by execution; capped searches are UNKNOWN, never failures. A refinement omits fill edges incident to no deficit; such edges cannot belong to a minimum-cardinality fill. A third generator adds randomized deletion orders to find positive weak spanning subgraphs before recursion. It uses the same numerical seed but starts at order 11, so it is an independent sample, NOT replay of the earlier graph sequence.

The search uses an existential choice of eligible vertex and minimum fill, the weakest natural interpretation of the source reduction. It could refute stronger choice quantifiers only with an explicit additional audit; no such refutation is claimed. C5 reducing to C4 would merely be a smallest-order exception and was not counted or formalized.

## 362434: colored-angle matrix and literal combinatorial test

For an edge uv of color c, the row of [R M] has p_u-p_v at u, p_v-p_u at v and -||p_u-p_v||² in the color-c column. Over a prime field, full row rank at an integer realization proves that the corresponding polynomial minor is not identically zero over the rationals. Failure of rank at a sampled realization does NOT prove generic dependence.

For rank-deficient samples the scripts enumerate choices of one deleted edge of each color other than j, for every j. The complement must have 2n-3 edges and at most 2|S|-3 edges in every vertex subset S of size at least two. This is the literal Laman-basis test behind Conjecture 3.6. No sample passing that condition remained rank-deficient, so no putative counterexample was promoted. The first sweep sampled 4,000 instances per order 4–8; the extension sampled 500 per order 9–12, with only 2–4 colors in the latter sweep. They are not exhaustive colored-graph censuses. No characteristic-p deficiency is treated as a real dependency proof.

## 362310: structured spectral diagnostic

The G_c(s,t) constructor follows the source loose path of length s+t, with c pendant hyperedges at every internal path vertex except u_s. A rooted tree of root degree c is attached at u_s; its root branches meet only at that root, as required in the source construction. Replacing every ordinary tree edge by a k-edge with k-2 fresh leaves gives k=2 and k=3 uniform examples. Random rooted bases have 4–14 vertices, root degree 2–4 and more than c edges. Each base was tested at six ordered (s,t) pairs under (s,t)->(s+1,t-1).

BFS gives distance matrices. Floating positive power iterations return approximate Collatz ratio widths, not outward-rounded exact intervals. All 2,292 comparisons were positive; no spectral proof or refutation follows. The source's c=1, path-branch, and many-pendant-edge cases were checked as prior ingredients before this computation. A full proof still needs an estimate on the Perron mass of arbitrary central branches, or a new exact reversal outside those cases.
