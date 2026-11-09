# Mathematical routes and credit limits

No claimed discovery and no Lean endpoint.

## 365572: zero-sum partitions

Let R be the complement of 0 and the unique involution. R is closed under negation and has even cardinality N, with no fixed points under negation. Every prescribed part m >= 2 is a sum of 2s and 3s: an even part uses only 2s and an odd part uses one 3 and then 2s. Therefore checking every partition using parts 2 and 3 suffices for every prescribed partition. Since N is even, the number of 3s is even.

A stronger sufficient finite certificate is a packing of floor(N/6) disjoint six-element sets T union (-T), where T is a zero-sum triple and T is disjoint from -T. Given 2r triples in a refinement, use r such six-element sets, take T and -T as separate triples, and partition the remaining inversion-closed set into opposite pairs. Coalescing according to the prescribed refinement realizes the original partition.

The first exact-cover program directly enumerates every zero-sum subset for C2 x C3 x C3 and all 55 partitions of 16. It also checks six 2/3-part partitions for C4 x C3 x C3. The extension program uses the sufficient six-element certificates, retaining exact bit masks. Completed certificates are recorded in groups-extended.json; any interrupted group is not covered. This is the source's Skolem/inversion-pair type mechanism, not a new unrestricted theorem. It is not a candidate and needs no Lean investment. The general existence of these certificates is unproved here.

## 366011: radial Moore status

The source's invariant is total ordered-pair distance sum, not just a distinguished vertex's status. For degree d and diameter 3, graphs have d^2 + 1 vertices and radius 2. The constructed graph has total status 3d^4 - 4d^3 + 3d^2 - d. Proposition 3.4 contains an inconsistent displayed central-vertex local formula, but its distance description gives d(2d-1), and the total-status formula is consistent. We use the latter: no endpoint-correction claim.

Fix a root, d children, and d-1 leaves under each child, then add an arbitrary (d-1)-regular simple graph on the d(d-1) leaves. Degrees and radius at most 2 are built in. Bit-mask breadth-first search computes all distances through 3. A penalty excludes pairs at distance >=4. Leaf 2-switches preserve degrees. The start is a randomly relabelled circulant, independent of the source's clique/matching construction. We optimize status using simulated annealing and retain exact attempts, admissible evaluations, degree, order, seed and wall time. Repeated states are possible: evaluation counts are not counts of distinct isomorphism classes. No search here is exhaustive and no maximality theorem follows.

## 366321: rainbow arborescences

The source permits arc-disjoint coloured copies, so identical underlying arcs of different colours are separate parallel arcs. Every colour class is enumerated as a rooted tree via parent maps whose iterated parents reach its unique root. Colour permutations do not affect existence, permitting combinations with replacement of underlying directed trees. A rainbow choice of n-1 arcs is an arborescence exactly when the heads are distinct and all vertices are reachable from the remaining root. We enumerate such choices. Exhaustive coverage is n=2,3,4; n=5 uses only a seeded sample. No prescribed-root hypothesis is silently imposed. Verification for k=n-1 also covers k>n-1 at the same orders by dropping colours. This is finite validation only. The latest paper proves the undirected-cycle case; extending that proof to all digraphs is not established here.

## 357557: lattice embedding diagnostic

Take P with ordered vertices (2,0),(0,2),(-2,0),(0,-2). Candidate image vertices are distinct integer points of [-3,3]^2 of squared norm at least 4. Each consecutive edge has squared length at most 8. For a point p and its two neighbours a,b, put u=a-p, v=b-p. The origin is in the interior of p+cone(u,v) exactly when det(u,v) is nonzero and the two Cramer numerators det(-p,v), det(u,-p) have its sign. All these are exact integer tests. Pairwise edge and diagonal lengths test isometry to P. The diagnostic is a tiny rational subfamily in dimension two; it does not approach the unrestricted higher-dimensional conjecture. Source Theorems 4.4, 4.5 and 4.7 already handle substantial special cases.

## Public counterparts, not discoveries

364985: source Theorems 4 and 5 and Corollary 6 settle the edge part; its introduction credits the vertex part to Boutin et al. (2022).

365076 and 365077: source Theorem 3 and Section 3's recursive constructions refute the formulas. Never re-use these constructions for credit.

365295: Cheng 2610.06445 Theorem 1.3 gives full scope. Its proof combines the k>=10 counting bound with Hou-Zhao's k<=12 cases and duality; this is a located public proof, not independently certified here.

365523: Zheng 2601.04514 Theorem 3.3 and Corollary 3.4 explicitly prove the target. Section 3.1 diagonal-similarizes to a stochastic tensor, uses the Macaulay resultant quotient, semisimplicity for the stochastic matrix, and the source's lower bound. Read as public prior proof; not independently re-proved or formally audited here. Fan's current version still presents a Smith-elementary-divisor reformulation; that tension does not create a new candidate.

365579: Lean Pool's MainTheorems.mainTheorem gives primitive permutation groups of every base size >=2 with two vertices having no common neighbour. Source Theorem 6.7 gives equivalence with the almost-regular-orbit formulation. Indeed if N(alpha) is a union of nonempty almost-regular suborbits and N(alpha) intersects N(beta) trivially, every such suborbit is missed by N(beta). Public Lean statement and adjacency bridge read, no external replay.

357395: Cassaigne-Espinoza-Rigo-Stipulanti 2602.21895 Corollary 13. Proposition 11 identifies the first difference as a Toeplitz word; Proposition 12 proves uniform recurrence passes both ways between a binary word and its first difference; Lemma 4 transfers to the sibling sequence. All relevant proof passages were read. No finite-prefix search is needed after this exclusion.

366341: Paudel-Sellers-Wang 2503.12583 Theorem 1.2 and Corollary 1.3 explicitly settle the exact printed conjecture, using N=57 and the substitution n -> t^2 n+t^2 j/p. The primary target source's latest version already reports the resolution.

366405: Paudel-Sellers-Wang 2505.21989 Theorem 1.4 gives Rbar_4,9(4n)=0 mod12 for every n>=1, stronger than the target. Its proof in Section 5 uses elementary q-series dissections, separates mod4 and mod3 and extracts even coefficients twice. The source quantifier expression is 4(ell*n+k), a positive multiple of 4, so full scope is immediate. No numerical work is necessary after locating the proof.
