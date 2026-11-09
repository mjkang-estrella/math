# Ordinary proof of MathDB 342414 refutation

A cubic counterexample to edge-pattern convex domination

DRAFT • 2 November 2026<br/>AI-assisted research manuscript; no human authorship or affiliation is asserted. Prepared within the MathDB research campaign. Submitted for independent review; zero acceptance credit is assigned here.

Abstract

An eight-vertex edge-rooted pattern refutes Conjecture 2 of Pirot and Sereni [1] (MathDB 342414), also Conjecture 1.5.1 in Pirot’s thesis [2]. Its uniform maximum-independent-set occupancy vector is (2/5, 14/5, 4/5). The positive rational vector (1/1000, 7/27, 1/3) has value 67027/67500 on this pattern, while its value on every acyclic cubic pattern of depth 2 is at least 3001/3000. Thus no finite real convex combination satisfies the weaker implication required for e(P) by the conjecture. A complete Lean certificate proves the negation at universe zero. The source’s selected optimizing vector and its colouring bounds are unaffected. The bounded literature investigation establishes no priority claim.

1. Source definitions and the conjecture

All graphs here are finite and simple. In Definition 1 of [1], a vertex-rooted pattern of depth r has every vertex at distance at most r from its root. Its layers are the sets at each distance. It is d-regular when degrees are d except possibly in the deepest two layers, where degrees are at most d. Section 4.2.2 extends the definition to an edge root uv: the distance of x from the root edge is min(dist(x,u), dist(x,v)), and the depth is the largest such distance. The two endpoints therefore form layer 0. We use exact depth for the edge-rooted family. Finite depth ensures connectivity; girth is the shortest cycle length, with value infinity for a forest.

Write Lᵢ(P) for layer i and M(P) for the family of independent sets of largest cardinality. Definition 2 uses a uniformly random member I of M(P), so eᵢ(P) = E|I ∩ Lᵢ(P)|. Equivalently, eᵢ(P) is the sum of these occupancies over M(P), divided by |M(P)|. These are maximum independent sets, not arbitrary inclusion-maximal sets. The family is nonempty since P is finite. The source also records n(P) = |M(P)| to support recursive computations.

For vectors e and e′, the source calls e weaker than e′ when, for every strictly positive rational vector a, a·e′ ≥ 1 implies a·e ≥ 1. It separately defines relatively weaker by restricting to non-increasing test vectors. We use the unrestricted weaker relation. Our separating vector is increasing and does not address the relative variant.

Let T′ᵣ(d) denote the acyclic edge-rooted d-regular patterns of depth r. Conjecture 2 asserts that if P is such a regular pattern with girth 2r+2, then there exist T₁,…,Tₘ in T′ᵣ(d) and real λⱼ in [0,1], with Σλⱼ = 1, for which e(P) is weaker than Σλⱼe(Tⱼ). The same combination must work for every positive rational test vector. The surrounding degree and depth ranges include d = 3, r = 2, which suffice for a refutation.


--- PAGE ---


2. The pattern and exact separation theorem

<b>Theorem.</b> There is a 3-regular edge-rooted pattern P of exact depth 2 and exact girth 6 for which no finite real convex combination of constraints from T′₂(3) satisfies the implication in Conjecture 2. Specifically, put a = (1/1000, 7/27, 1/3). Then a·e(P) = 67027/67500 &lt; 1, whereas a·e(T) ≥ 3001/3000 for every T in T′₂(3).

<b>Construction.</b> Take vertices 0,…,7, root edge 01, and edges 01, 02, 03, 15, 17, 34, 46, 56. The cycle is 0-1-5-6-4-3-0; vertices 2 and 7 are pendants attached to 0 and 1. The layers are {0,1}, {2,3,5,7}, {4,6}. Roots have degree 3 and every other vertex has degree at most 2. The cycle is the only cycle, since pendants occur in none, so the girth is exactly 6. This verifies every regularity, depth and girth condition.

<b>Maximum sets.</b> For an independent subset J of the six-cycle, add all available pendants. Its resulting size is |J| + 2 - |J ∩ {0,1}| = 2 + |J ∩ {3,4,5,6}|. The latter four vertices induce the path 3-4-6-5, whose independence number is 2. Thus no independent set has size more than 4. Its independent pairs are {3,6}, {3,5}, {4,5}. For the first pair root 1 is optional and root 0 forbidden; for the second both roots are forbidden; for the third root 0 is optional and root 1 forbidden. Adding every available pendant gives exactly the following five size-4 sets.

Maximum independent set | (layer 0, layer 1, layer 2)

{1,2,3,6} | (1,2,1)

{2,3,5,7} | (0,4,0)

{0,4,5,7} | (1,2,1)

{2,4,5,7} | (0,3,1)

{2,3,6,7} | (0,3,1)

Their total layer occupancies are (2,14,4), proving e(P) = (2/5,14/5,4/5). Direct rational arithmetic gives a·e(P) = 1/2500 + 98/135 + 4/15 = 67027/67500, less than 1 by 473/67500.

3. Classification of all the trees

Let T be an acyclic pattern with the stated cubic regularity at radius 2. Each root has exactly two neighbours other than the opposite root. Label the branches at the first root A,B and at the second C,D. No branches coincide: such a coincidence would close a triangle or a cycle across the root edge. Each branch has at most two further neighbours, its leaves. A leaf cannot be a root or another branch, or belong to two branches: the already present root-and-branch paths would then yield a cycle. Similarly there are no extra edges among these vertices beyond their parent edges. Every vertex lies in one of these blocks by the depth bound.

Consequently T is rooted-isomorphic to the canonical tree specified by four counts (kA,kB,kC,kD) in {0,1,2}⁴. Conversely, each count tuple gives an acyclic root-cubic pattern of depth at most 2. These 81 labeled forms need not be pairwise non-isomorphic. The all-zero tuple has depth 1; the other 80 have exact depth 2. Checking all 81 is a harmless enlargement. The bound of 14 vertices is a consequence of this classification, not a restriction imposed on T.


--- PAGE ---


4. Exact evaluation of the 81 forms

Here is a closed evaluation rule that includes multiplicities in the uniform distribution. For k = 0,1,2, put m(k) = max(1,k), c(k) = 1,2,1 respectively, and let (b(k),ℓ(k)) equal (1,0), (1/2,1/2), (0,2). When a parent root is absent, its branch star has maximum size m(k), c(k) choices, and mean layer occupancies (b(k),ℓ(k)). When the root is present, the branch is absent and all its k leaves are present, with one choice. Independent choices in different stars multiply.

Consider the three allowed root states s = (0,0),(1,0),(0,1). For each branch j let tⱼ be its parent’s state. Set<br/>qₛ = s₀+s₁ + Σⱼ[tⱼkⱼ + (1-tⱼ)m(kⱼ)],<br/>Cₛ = ∏ⱼ c(kⱼ)<super>1-tⱼ</super>,<br/>vₛ = (s₀+s₁, Σⱼ(1-tⱼ)b(kⱼ), Σⱼ[tⱼkⱼ+(1-tⱼ)ℓ(kⱼ)]).<br/>Put Q = maxₛqₛ. Then e(T) = (Σ<sub>qₛ=Q</sub> Cₛvₛ)/(Σ<sub>qₛ=Q</sub> Cₛ). Indeed a maximum set must optimize each star conditional on its roots; only states with maximum qₛ survive, and Cₛ is their exact number. This proves the rule without reliance on a numerical optimizer.

For compactness the table gives 810000(a·e(T)). A row gives kA kB and a column kC kD. Thus every entry divided by 810000 is the desired exact value. Symmetries account for repeated entries; labels are retained to display all 81 forms.

AB / CD | 00 | 01 | 02 | 10 | 11 | 12 | 20 | 21 | 22

00 | 840000 | 810270 | 1065405 | 810270 | 960810 | 1230810 | 1065405 | 1230810 | 1500810

01 | 810270 | 810405 | 1080486 | 810405 | 990810 | 1260810 | 1080486 | 1260810 | 1530810

02 | 1065405 | 1080486 | 1360540 | 1080486 | 1290810 | 1560810 | 1360540 | 1560810 | 1830810

10 | 810270 | 810405 | 1080486 | 810405 | 990810 | 1260810 | 1080486 | 1260810 | 1530810

11 | 960810 | 990810 | 1290810 | 990810 | 1020810 | 1300810 | 1290810 | 1300810 | 1572810

12 | 1230810 | 1260810 | 1560810 | 1260810 | 1300810 | 1590810 | 1560810 | 1590810 | 1870810

20 | 1065405 | 1080486 | 1360540 | 1080486 | 1290810 | 1560810 | 1360540 | 1560810 | 1830810

21 | 1230810 | 1260810 | 1560810 | 1260810 | 1300810 | 1590810 | 1560810 | 1590810 | 1870810

22 | 1500810 | 1530810 | 1830810 | 1530810 | 1572810 | 1870810 | 1830810 | 1870810 | 2160810

The smallest entry is 810270, so a·e(T) ≥ 810270/810000 = 3001/3000. For example tuple 0001 attains it. Substitution into the displayed rule checks every table entry by rational arithmetic; receipts also compare the rule with an independent enumeration of all vertex subsets for all 81 forms.

5. Convex separation and robustness

For any finite real weights λⱼ ≥ 0 summing to 1, linearity gives a·Σλⱼe(Tⱼ) = Σλⱼ(a·e(Tⱼ)) ≥ 3001/3000 &gt; 1. Yet a·e(P) &lt; 1. The strictly positive rational a therefore falsifies the implication defining weaker for every proposed combination. This proves the theorem and refutes the universal conjecture.

If depth at most 2 is used while retaining regularity at radius 2, the sole additional tree is the all-zero form. Its occupancy is (0,4,0) and value 28/27 ≥ 1. There is no depth-0 example because the roots must have degree 3. This convention robustness is ordinary mathematics here, not an additional Lean endpoint.


--- PAGE ---

