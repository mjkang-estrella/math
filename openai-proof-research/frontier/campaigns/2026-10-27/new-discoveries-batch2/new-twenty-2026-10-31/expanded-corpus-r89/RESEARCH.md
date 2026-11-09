# Mathematical investigations and qualification limits

This is an investigator report, not an acceptance decision. No claimed campaign credit, no Lean endpoint, and no claim of a multi-hour complete literature investigation. All numerical checks below are ordinary diagnostic programs. The short elapsed pass does not satisfy the assignment's requested several-hour depth; this limitation must accompany any handoff.

## 364079: exact counterexample, disqualified as a routine source consequence

The primary source is Mitrović–Stojadinović, arXiv:2407.18608v3, §§2, 3.2–3.3, and Conjecture 5.1. Its digraph has an arrow i→j exactly when i≤P j; loops have no effect on listings. Its function is the sum of fundamental quasisymmetric functions indexed by the descent sets of all vertex listings.

On {0,1,2,3}, take strict relations

P: 01, 02, 03, 12, 13;
Q: 01, 02, 03, 13, 23.

Both are transitive, irreflexive, asymmetric relations. P has minimal set {0} and maximal set {2,3}, whereas Q has minimal set {0} and maximal set {3}. Thus the extremal-element sums are 3 and 2.

Listing all 24 permutations gives the same fundamental-basis coefficient vector for both, indexed by descent bitmasks 0 through 7:

(2, 4, 6, 2, 4, 4, 2, 0).

Consequently their literal Redei–Berge functions are equal in every number of variables, not merely equal at sampled evaluations. `scripts/redei_verify.py` independently counts the monomial coefficients in four variables as a diagnostic cross-check; the listing signature proves the unbounded formal-function equality mathematically. `outputs/redei-verification.json` records the full data.

However, P = C2 ordinal-sum A2 and Q = C1 ordinal-sum A2 ordinal-sum C1. The primary source defines ordinal sum as its poset Hopf-algebra multiplication, proves that g is a morphism in Theorem 3.4, defines U as its universal morphism in Definition 3.5, and gives U(C2)=U(C1)^2 in Example 3.9(1). Multiplicativity into the commutative symmetric-function algebra therefore gives

U(P) = U(C1)^2 U(A2) = U(C1) U(A2) U(C1) = U(Q).

This is an explicit full-scope bridge from the source's existing theorems to an exact negation of its conjecture. The assignment excludes routine consequences with explicit bridges. Thus this counterexample is recorded but is **not an eligible discovery**. No worldwide priority or earlier explicit publication of this particular four-point example is asserted. Stop this route; do not use the n=5 or n=6 variants for additional credit. No Lean investment was made after the routine-consequence exclusion.

## 366901: source fidelity and two search mechanisms

The survey arXiv:2501.19385 gives Conjecture 5.29. The actual cited primary article is Chandran et al., *Colouring a graph with position sets*, Ars Math. Contemp. 26 (2026), #P4.06, DOI 10.26493/1855-3974.3454.a3c. The publisher article/PDF was fetched successfully. Conjecture 9.3 on pp. 24–25 includes both a sum and a product bound; this MathDB ID asks for the sum. Theorem 4.4 and its complete short proof show that every independent set is in general position when diameter ≤3, hence χ_gpi=χ. The same statement does not apply to monophonic position. The original article explicitly reports exhaustive checks through order 10, attributed to Erskine's private communication; our checks through six vertices add no new literature-level bounded result.

The checker treats disconnected graphs componentwise for path existence; infinity is not used in a false shortest-path equality. It lists all independent sets and rejects those containing three vertices on any shortest path (gp), or on any induced path (mp). Since being a position set is hereditary, exact subset dynamic programming computes the minimum partition into allowed sets. The complementary graph is formed on the same labelled vertex set. Through n=6, complement symmetry halves the space, apart from the one-vertex case. Maximum sum is n+1 for both invariants at each tested order.

A second search uses 400 seeded random graphs at each order 7–12, with six edge densities. It also found no counterexample. Random dense graphs are weak tests for the gp case because both diameters tend to be at most three. They also typically have perfect or near-perfect matchings in the complement.

A sharper obstruction-directed search uses Tutte-style barrier sets S and many odd components in G−S, with partly filled cliques and varied attachments to S; the intended orders are 11–15. Its exact realized coverage is in the `ng-tutte` output, not an exhaustive graph census.

Proof attempt: any pair of nonadjacent vertices is an independent position set, so χ_pi_i(G)≤n−ν(complement G). If both graphs have maximum-size matchings, this proves the desired sum bound. A putative obstruction therefore needs matching deficiency on one side. This motivates the barrier search. The matching bound alone is insufficient: for K1,3 and its complement the matching numbers sum to only 2, giving the loose bound 6 rather than 5; the three leaves nevertheless form an allowed position class. A proof would need a position-compatible replacement for matching pairs across a Tutte barrier. No such lemma was proved. Avoid assuming that induced-subgraph position classes remain valid in the larger graph: new paths through the deleted barrier can invalidate them.

## 369905: exact product checker and failed proof extensions

The original arXiv:2508.16338v1 defines an isolating set S by independence of G−N[S]; Conjecture 6.3 is the literal universal Cartesian-product inequality. The earlier domination and independence-domination questions in Problems 6.1–6.2 are different, stronger statements and are not substituted for this endpoint.

For a product graph, the decision checker searches isolating sets of size strictly below iota(G)iota(H). Given an uncovered edge uv, every completion must contain a vertex in N[u]∪N[v]. Branching over that union is complete. Each step updates the union of closed neighbourhoods, and a branch succeeds precisely when the remaining vertices are independent. This is a sound exact ordinary algorithm, not a certified Lean checker.

The early search checks 9,870 pairs from 140 labelled factors with isolation number at least 2 (all such factors through five vertices, plus 70 seeded six-vertex factors). A subsequent degree-preserving canonicalization yields 29 isomorphism representatives for all hard factors through six vertices, and checks all 435 unordered pairs. It then checks 2,494 additional pairs from 86 seeded factors of orders 7–10 against those 29 representatives. No violating isolating set was found.

The omitted factors with iota≤1 are settled by the following elementary projection argument. If S isolates G square H and H is nonempty, its projection A on G isolates G: otherwise choose an edge uv outside N_G[A]; for any h, the product edge (u,h)(v,h) is outside the product closed neighbourhood of S. Thus iota(product)≥iota(G), and symmetrically ≥iota(H). Empty factors have product isolation zero. This proves the product inequality when either factor has isolation number at most one. This routine helper does not earn credit and was not presented as a full endpoint.

The projection argument gives a maximum, not a product. Counting projected vertices with multiplicity does not strengthen it: many selected product vertices can share their first or second coordinate. A full proof needs a disjoint charging or packing argument beyond that projection. The source's packing-type lower bounds do not directly give the product of isolation numbers. No full proof or counterexample was obtained.

## Other finite routes

* **368045:** enumerate cubic bipartite incidence row systems with no pair of rows meeting twice (girth at least six). Normalize the first row to {0,1,2} and sort rows; this covers isomorphism types because column and row relabelling preserve every tested property. At bipartition size 7 there are six normalized systems, all Heawood realizations and 2-factor Hamiltonian. At size 8 there are 120 systems, none 2-factor Hamiltonian. Also check all normalized three-shift bipartite circulants through 30 vertices: 264 girth-six systems, six 2-factor-Hamiltonian survivors, all at order 14. Perfect matching complementation enumerates every 2-factor in a cubic graph. Cyclic connectivity was not separately certified: eliminating every non-Heawood 2-factor-Hamiltonian graph in these bounded spaces is already a sufficient negative search. No general classification follows.
* **369842:** source Conjecture 4.3 says the **dual** of an upper combinatorially uniform geometric lattice is TN. The raw MathDB paraphrase drops “dual”; source scope governs. Enumerate all nonempty simple binary point sets in ambient ranks 2 and 3 and 2,000 seeded point sets in ambient rank 4. Form flats by intersections with vector subspaces, compute ranks, check rank uniformity in the dual, and compute every minor of its finite R matrix with integer arithmetic. The outputs give 7/7, 78/127 and 141/2000 upper-uniform cases, all with nonnegative minors. This is not a search over all matroids or all geometric lattices. A general proof would need TN for all admissible upper interval rank arrays, beyond the classified triangular/Dowling families.
* **374802:** recover Equation (7) literally as v=ell(ell−2)k/((ell−1)^2−k), together with symmetric-design lambda=k(k−1)/(v−1). Enumerate integral candidates with v≤200 and ell≤15; a parameter solution does not prove a design exists. Build the quadratic (16,6,2) Menon difference-set design and verify all pair counts and a four-colouring. Independently enumerate all 1,820 four-subsets, retain the 60 that meet every block in zero or two points, and enumerate all partitions into such classes: all 105 satisfy 0-ULSE. This known-family success does not settle existential sufficiency for arbitrary parameter triples. Noncolourability of one design would not refute the conjecture, which asks for some design with those parameters.
* **364184:** read Definition 2 (sat_m inserts only the new least edge) and Conjecture 60. Enumerate every edge-ordering for P3 and all six edge orders of P4, and increasing-size ordered hosts until the first saturation witness for target order through host order 5. The output contains exact small sat_m values. These constants cannot distinguish Theta(n) from a superlinear function. Semisaturation hosts cannot silently be promoted to G-free saturation hosts; that missing freeness argument remains the source gap.
* **365133:** implement the source's non-conflict condition exactly with alpha=1, beta=2, alpha+beta=3 and XOR conservation after contraction of each complementary 2-factor cycle. Search generalized Petersen G(n,k), 5≤n≤9, 1≤k≤floor((n−1)/2). Only G(5,2) fails among the 14 tested graphs; its six matchings and 1,458 assignments are all checked. This is the already-known Petersen obstruction, with cyclic connectivity five, not an infinite cyclically six-connected family. Even a new single six-connected obstruction would still need an infinitude construction.
* **376075:** enumerate all labelled graphs through six vertices and every maximal independent set, then compute exact transversals for each integer size threshold. At order 6 the largest possible transversal sizes for thresholds 1 through 6 are 6,3,2,1,1,1. Finite maxima cannot refute an o(n) claim. Disjoint replication of a fixed graph is ineffective: requiring a vertex set to meet every product of independent choices can be achieved by hitting all choices in one fixed component, yielding a bounded transversal. A counterexample requires a correlated growing family with a linear transversal number at a fixed positive density.

## Known-source exclusions and inaccessible scope

357342 is already refuted in source Example 7.2, using lush hedges; the explicit 31-vertex example has multiplicities (11,7,6,2,2,1,1,1), with the stated split impossible. The Example 7.2 proof passage, its maximal-length mechanism and Theorem 6.1 dependency were read; this is not an independent audit of the long proof of Theorem 6.1.

361290 is already refuted in Liu–Ning, Theorem 5.1. Section 5 constructs clique-first chains of independent layers with mass 1/2−O(k^5/n^3); for fixed k≥3 this violates the conjectured deficit of order n^(−1/2). The two claims and mass calculation were read. No smaller witness earns new credit.

361700 is already refuted in source §3, Theorems 3.3 and 3.5. The first bridges real-zero amalgamation to polymatroid amalgamation; the second supplies the contradiction for relaxations of the Fano matroid. The complete short submodularity contradiction was read. This is not a fresh polynomial counterexample.

375737 is already refuted in Larson, Example 1.4 and Theorem 1.5 (rank 9 on 18 elements). The split-pair invariant can take values 3,7,9 but not 5, and exchanges change it by at most 2. The four exceptional orbit representatives and complementary-basis exclusions were read. No complete new matroid enumeration was undertaken after this source exclusion.

360676 has a published admissible/natural-action result in Theorem 1.3; the paper explicitly notes that Schleimer does not assume that action. Do not declare the literal broader version solved from the admissible theorem.

365149 was screened in the old r130 notes; it was not an accepted result. Source Conjecture 3.9 and its illustrative dictionary/subset-generator tables were inspected. The paraphrase alone does not define a complete uniform generative algorithm for SG. No arbitrary XOR-word test is represented as a test of the source conjecture, and no duplicate promotion is made.

357663 is an asymptotic labelled-speed question about induced subgraphs of hypercubes. Source §5.1 supplies the n^(2n) encoding and asks for c^n n!, leaving a genuine exponent-level gap. 365171 is the semi-minimal Cayley question in source Conjecture 11, distinct from the no-lonely-colour conjecture disproved in the paper. 368489 is source Conjecture 1.4, not one of the triangle cases proved there. 368589 and 368590 are source Conjectures 4.2 and 4.3, respectively, beyond Theorem 4.1's restrictive isoperimetric setting; testing a few spherical coordinates cannot certify global degree-one uniqueness. These are parked with explicit general gaps, not excluded as known or cleared as novel.
