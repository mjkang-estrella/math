# HOLD — original Problem 2.12 / survey Problem 30

No full ordinary resolution; no PROOF designation, no new outcome. Counts9/39/next40 unchanged.

## Attribution, exact scope, chronology

The original located question is Głąb–Marchwicki, *Cardinal functions of purely atomic measures*, arXiv:1911.01206v1, submitted4November2019, printed Results Math75:141(2020), Problem2.12, PDFp7. It asks whether existence of natural numbers n_k→∞ with f⁻¹(n_k) nonempty for every k implies f⁻¹({ω,c}) nonempty. This is the NEGATION of the requested existence question. There is no requirement that every natural cardinal occur. The source convention is a summable positive sequence; signed absolutely summable sequences can be converted to positive terms by flipping the corresponding bits, with zero atoms discarded. We work literally with strictly positive terms indexed by N, not the eventually-zero extension used for finite sequences in2025.

Głąb–Prus-Wiśniowski, arXiv:2512.17285v1, submitted19December2025, §6 Problem30 PDFp11, attributes it to reference22, that2020 paper: “Does there exist a sequence x such that the range of F_x contains an unbounded sequence of natural numbers but neither ω nor c?” Problem29 is the larger range classification; Problem31 is the separate perfect-subset question. Neither is substituted for Problem30.

Marchwicki–Żmija, arXiv:2508.13016v1,18August2025, §4 PDFp6 and §5 PDFp11, expressly says the finite-unbounded/no-infinite case is unknown and cites original Problem2.12. This is actual body evidence, not an abstract inference. Current arXiv landing pages for all three show only v1 at retrieval; title/author searches found the2019 and2025 papers, but this is not exhaustive citing-literature clearance. Denied public-registry intervals remain PARKED; no present GitHub head or global novelty clearance is claimed.

## Exact additive reductions (helpers, uncredited)

Write S_x(ε)=Σx_i ε_i, and F^(N) for the cardinal function after deleting coordinates1,…,N, extended as zero off its achievement set. Partitioning a fiber by its first N bits gives, as a disjoint cardinal sum,

F_x(t)=Σ_{a∈{0,1}^N} F^(N)(t−Σ_{i≤N}a_i x_i).

Thus a tail bound M gives the global bound2^N M. Conversely any tail fiber injects into a global fiber by extending with zeros. Consequently global unboundedness forces unboundedness on EVERY tail; if all global fibers are finite, every tail fiber is finite as well. Original Lemma3.7 contains the boundedness equivalence. This reduction is not new.

Formalize the finite hitting condition using *reduced* equal-sum relations: d∈{−1,0,1}^N, d≠0, Σd_i x_i=0, support={i:d_i≠0}. If every such support meets a fixed finite H, the restriction to N\H has no collision. For fixed t and a choice on H there is at most one tail, whence F_x(t)≤2^|H|. “Equal-sum sets meet H” would be weaker and ambiguous because common coordinates cancel. The correct condition is that their symmetric difference meets H. An injective complement and this reduced-support hitting condition are equivalent. It is sufficient for boundedness, not necessary.

If there are infinitely many pairwise disjoint reduced relation supports, continuum multiplicity follows even if each support is infinite. For each j take disjoint nonempty A_j,B_j with the same sum s_j and pairwise disjoint A_j∪B_j. Positivity and disjointness give Σs_j≤Σx_i. For each η∈{0,1}^N choose A_j or B_j and unite. All resulting subsets have sumΣs_j, and distinct η give distinct subsets. Absolute convergence justifies grouping; the continuum upper bound is the size of the domain. No finite-support assumption is needed for this implication. What is unavailable is extraction of disjoint supports.

## Exact obstruction: arbitrarily deep collisions need not branch

Let x_i=2^(−i). If two binary representations differ first at k, their difference at k has magnitude2^(−k), while the whole remaining tail has exactly that mass. Equality forces ALL later differences to have the opposite sign and absolute value1. Every nonzero reduced relation therefore has support exactly{k,k+1,…}. No two such supports are disjoint. Each fiber has at most two points: after the first differing digit both tails are forced; equivalently the binary expansion is unique except for terminating dyadic ambiguities. Endpoints0 and1 have one representation. Interior dyadics have two. Every tail is a scaled copy, hence has collisions arbitrarily far out, but the global bound is2. No finite H meets every reduced relation. This also refutes the converse “bounded fibers imply an injective tail.” It does NOT refute the desired implication with UNBOUNDED finite fibers.

Compactness of pairs of colliding representations only yields a limiting equal pair, which may be the same point. For the dyadic relation at k, both colliding points approach0∞ as k→∞. Compactness supplies no uniform separation or surviving binary branching.

## Exact countermodel to the general compact-map claim

Let C={0,1}^N and p=0∞. Set U_n=0^(n−1)1C, n≥1; these clopen components partition C\{p}. Partition each U_n into n clopen cylinders V_(n,j). For n≥2, use suffix prefixes1,01,…,0^(n−2)1,0^(n−1); for n=1 use the empty suffix prefix. Each V_(n,j) is homeomorphic to C by erasing the displayed prefix.

Let K be the usual ternary Cantor set and K_n=4^(−n)(2+K), lying in[2·4^(−n),3·4^(−n)]. Define f(p)=0 and map each V_(n,j) homeomorphically onto K_n using the standard binary-to-ternary homeomorphism. The target Y={0}∪⋃K_n is compact, perfect and zero dimensional. On each U_n the map is continuous; at p it is continuous because sup K_n→0. Every t∈K_n has EXACTLY n preimages, one in each V_(n,j), and0 has exactly one. No other fibers occur, including endpoints of K_n and the only intercomponent accumulation point0. Hence a continuous surjection from Cantor space to a compact subset of R can be finite-to-one with unbounded fibers. Y is itself homeomorphic to Cantor space. This defeats any proof using only compactness/continuity. It is not a subsum map: no additive product structure has been supplied.

## Sustained constructive tests and their failures

1. The2025 Lemma2.1 scales a FINITE sequence y so its distinct subsums are farther apart than the total mass of x. Its translated copies of A(x) are disjoint and multiplicities multiply. The finite minimum gap δ>0 is indispensable. An infinite compact prefix achievement set has no positive minimum gap.
2. Infinitely many independent separated blocks with any nontrivial within-block multiplicity fail, even with asymmetric scale separation: fix one collision value per block and independently choose its two representations. The preceding disjoint-support proof produces c at their convergent sum. Smallness and asymmetric separation do not remove that point. Uniqueness of the empty and full endpoints does not help.
3. A conditional-cluster construction imitating f above would need a “first active coordinate” to deactivate every later independent ambiguity. A subsum map adds all coordinates independently; putting one finite cluster on each separate scale activates them simultaneously rather than conditionally. We have no additive realization of the compact countermodel.
4. Original Theorem3.8 proves the negative answer under x_n≤r_n for every n (and, by finite-prefix splitting, eventually): finitely many strict inequalities give a bounded dyadic tail; infinitely many allow a sparse sequence k_j with Σ_{j≥l}x_(k_j)≤r_(k_l), and tail interval-filling supplies distinct representations of one sum. The proof body was read. Corollary3.9 forces any proposed counterexample to have x_n>r_n infinitely often. This eliminates interval/multi-interval achievements, but not Cantor/Cantorval cases. One cannot remove the interval-filling hypothesis; the same paper's Remark3.10 gives a Cantorval with infinitely many strict reverse inequalities and range{1,2}.

Next useful calculation: find a genuinely additive substitute for conditional clusters, or show that unbounded tail fiber sizes force a compatible branching family of SAME-SUM cylinders. The sets of points with fiber size≥m are not generally closed, so a nested compact-set argument needs an additional additive invariant. Neither construction nor invariant has been established. No finite computation in this packet is claimed to settle that gap.
