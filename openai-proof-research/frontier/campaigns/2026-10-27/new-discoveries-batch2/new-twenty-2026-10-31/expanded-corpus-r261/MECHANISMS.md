# Ordinary research, zero accepted credit

These notes address only the fixed reservation. No Lean was run. No finite numerical search was run. A full ordinary argument below is not an eligibility or novelty finding.

## 324627: complete ordinary converse, excluded as a classical bridge

Read Latorre, arXiv:1212.1406v1, Definitions 5.7, 5.9, 5.12, 5.16, 5.17 and Lemma 5.19/Conjecture 5.20, pp. 29–35. The source requires an **integer nonnegative** cycle in the residual multisimplicial complex, not merely a real cycle. The distinguished facet has infinite capacity. Retain the source condition; the proof below does not need to weaken it.

Let g be feasible with g(T)>f(T). In the original oriented facet basis put h=g−f. Its boundary is zero. For each h_sigma>0 use sigma with coefficient h_sigma; for each h_sigma<0 use the opposite orientation −sigma with coefficient −h_sigma; discard zero coefficients. The resulting positive real chain z has zero boundary and contains T positively. Every selected orientation is residual: in the forward case g_sigma>f_sigma implies c_sigma−f_sigma>0; in the reverse case g_sigma<f_sigma and g_sigma≥0 imply f_sigma>0, which is the reverse residual capacity. T itself is forward-residual because its capacity is infinite.

To respect Definition 5.17, form the integer boundary matrix A on this finite selected support. The point z is a strictly positive real vector in ker A. Gaussian elimination over Q produces a rational basis v_1,…,v_s of ker A and the same basis spans the real kernel (the ranks agree, as witnessed by the same nonzero minors). Write z=sum a_i v_i. Approximate each a_i by rationals sufficiently closely that every coordinate of sum q_i v_i stays positive; this is possible because the support is finite and its minimum coordinate is positive. Multiply by a common positive denominator. This gives a positive integer vector in ker A, still containing T. It is the required augmenting cycle.

This proves the exact finite-network converse, including the integer bridge, without total unimodularity or integrality of f,g,c. It is precisely the standard feasible-direction construction for a rational linear constraint matrix followed by rational-kernel density. No decomposition into embedded spheres, manifold cycles, or elementary circuits is required by Definition 5.17. Those stronger interpretations are not being solved. Exclude from campaign credit as a routine linear-algebra/classical bridge. No public exact earlier proof located is claimed; full later literature remains unchecked.

## 355928: complete ordinary counterexample, excluded as routine

Read arXiv:2208.14707v1, especially the definition of local antimagic labeling, the product constructions, Examples 2.1–2.3, and Conjecture 2.2. Let G=K4 and H=K2. Their lexicographic product is K8: two different pairs either differ in their G coordinate, whose vertices are adjacent, or have equal G coordinates and different H coordinates, which are adjacent. Here chi(G)chi(H)=8. The shortest odd cycle of G has length 3, so k=1; the purported right condition is 8=2·2+ceil(2/1)=6, which is false.

Label the edges ij, 0≤i<j≤7, in lexicographic order by 1,…,28. The eight sums are respectively 28,64,90,108,120,128,134,140. They are distinct, so this is a local antimagic labeling and gives chi_la(K8)≤8. Every proper vertex coloring of K8 uses eight colors, so chi_la(K8)=8. The asserted equivalence therefore fails.

This is a complete-graph product specialization and elementary labeling, not an eligible discovery. It is not the already accepted full-tree family 354228 or join family 365453, but family disjointness alone cannot establish significance. Those acceptances and same-source product recipes were explicitly checked; the exclusion stands independently. The journal body/corrections and related source references are not fully cleared. Do not formalize this for credit.

## 375537: sustained lift analysis and a precise conditional certificate plan

Sources read: Cranston et al., arXiv:2606.24685v1, introduction/Conjecture A, Section 2 (Theorem 2.1 and lift Lemma 2.5), cubic results in Section 3, even Eulerian case in Section 4, and contractibility discussion in Section 5. Esperet et al., arXiv:2512.17342v4, Sections 2.1–2.4, Theorem 2.3, Observation 2.5, Problem 2.6, K4 example, frozen-flow discussion, and Lemma 5.5/proof. Earlier v1–v3 are cached; version-specific review is limited to relevant conjecture/lift occurrences, not a full proof audit of all versions. Fixed orientations identify flows differing by reversal and value negation. A move changes values on one connected 2-regular cycle; it is not an arbitrary Eulerian subgraph move. The empty flow space is connected by the sources' convention.

First mechanism: difference of integer lifts in one residue fiber decomposes into directed cycles with changes ±k. This works, but is **already Lemma 5.5** of Esperet et al. Its bound is at most |E| moves. It earns no helper credit. It also does not lift an arbitrary modular adjacency, because the integer representatives on its cycle may force incompatible bounds.

Second mechanism: lift each modular edge after choosing suitable representatives. This reduces to an exact bounded-circulation feasibility problem, but feasibility is not proved in general. Importantly, it is wrong to check only shifts t and t−k: bounded representatives may differ by t+k or t−2k too.

The following is a sound finite certificate design, **without an asserted witness or a completed solution**. Root must decide whether to authorize Pi execution. For a finite simple graph with a fixed orientation, let B be the out-minus-in incidence matrix, k≥4, and M the complete finite set of nowhere-zero Z/k flows, represented by residues r_e in {1,…,k−1}. Build modular adjacency using the full simple-cycle list. This graph is F_mod.

For each r in M, its integer lifts are exactly

    f_e = r_e − k x_e,  x_e in {0,1},  Bx = Br/k.

Here Br/k is integral because r is a modular flow. Tutte's lift theorem makes each fiber nonempty; alternatively, a finite certificate can provide one x for every r and verify its equations. Lemma 5.5 makes each fiber connected.

Define Q on M by declaring r and s adjacent exactly when some adjacent integer lifts exist. Necessarily Q is a subgraph of F_mod (ignore loops). Conversely, collapsing the connected nonempty fibers shows that F_int and Q have identical component partitions after the projection. Therefore a connected F_mod but disconnected Q would refute the literal conjecture.

Here is an exact edge test for Q. If s−r is supported on the simple cycle C, choose a traversal and let epsilon_e be +1 or −1 according as the fixed edge orientation agrees with the traversal. There is a unique t in {1,…,k−1} such that s_e−r_e = epsilon_e t mod k on C. Every adjacent pair of integer lifts then has difference epsilon_e delta on C, zero outside, with

    delta in Z,  |delta|≤2k−2,  delta=t mod k.

This is a complete list of at most four integers. For each delta, test whether x_e in {0,1} satisfies Bx=Br/k and, on C,

    0 < |r_e − k x_e + epsilon_e delta| < k.

Outside C both representatives already agree. On each edge these conditions allow an explicitly computed subset of {0,1}; an empty subset certifies failure immediately. Otherwise write the subset as integral bounds l_e≤x_e≤u_e. A feasible **integer** x certifies a Q edge. A rational feasible x is sufficient for existence by the integral bounded-circulation theorem, but no unchecked solver assertion may enter the Lean endpoint.

For a negative certificate, produce a vertex subset S with

    sum_{v in S}(Br/k)_v > sum_{e outgoing S}u_e − sum_{e incoming S}l_e.

This directly contradicts Bx=Br/k and the bounds by summing vertex equations. For ordinary bounded circulation these cut inequalities are complete; Pi may use that standard theorem to generate cuts, but a refutation checker needs only their easy soundness direction.

A complete refutation packet would contain: graph adjacency/orientation; k; complete cycle enumeration or a proof every simple cycle is represented; a complete modular-flow enumeration (spanning-tree chord coordinates give at most (k−1)^b possibilities for cycle rank b); one integer lift per modular flow; an F_mod spanning tree with verified cycle moves; a nontrivial bipartition M=L∪R; and, for every modular edge crossing that partition, an empty-coordinate or cut witness for **each** allowed delta. All finite universal completeness claims must be proved. The nontrivial partition and supplied lifts exhibit integer flows on opposite sides; every integer move projects either inside a fiber or to a certified Q edge, so no integer path crosses.

Suggested bounded first execution, only if root authorizes: cycle rank b≤5, at most 8 vertices/12 edges, k in {4,5,6}, under explicit per-instance resource limits and early state-count rejection. This gives at most 5^5=3125 chord assignments at k=6 before filtering; cycle counts and cut-packet size are graph-dependent, not promised small. Source-known K4 obstruction, cubic bipartite cases, and Eulerian even-k cases must be rejected before interpreting a discrepancy as a discovery. The all-graphs conjecture is not reduced to this finite range, and a negative sweep earns zero credit.

Pi semantic modules would be literal signed incidence flows; source cycle adjacency; reduction mod k; exhaustive chord-coordinate bijection; cycle constant-difference lemma; a sound cut checker; reachability invariance under the supplied partition; and the final existential counterexample/negation of the universal statement. Finite computations must be kernel checked without native_decide, unsafe, added axioms, sorry, or admit. There is no witness yet. The full printed construction/figure-family comparison and current journal/correction sweep must be completed for any future witness, before qualification. No clearance is claimed here.

## 324588: strategy stealing does not yet prove a uniform constant

Read both arXiv versions and the public author-deposit revision dated 9 February 2014. The publisher PDF and HTML each returned status 202 with an empty body; neither is a journal-body read. The game ends at a maximal intersecting family of distinct k-subsets, and the payoff is transversal number, not the length of play. The desired constant is independent of both n and k.

Attempt 1: ignore the opponent's first set and play the other starting-player strategy. A later imagined move may be disjoint from that ignored set and therefore illegal. Increasing the claimed family shrinks the legal-move set. Although adding one set raises a fixed family's transversal number by at most one, the entire subsequent terminal family can change; terminal-payoff Lipschitzness under a phantom move is missing.

Attempt 2: after a collision, replace the illegal imagined set by a set intersecting the ignored set. A one-element repair can destroy an intersection with another claimed set whose only intersection was that deleted element. Repeating repairs can consume arbitrarily many elements of a k-set. Need a replacement lemma maintaining intersections with the full evolving family and changing terminal transversal number by a universal constant. No such lemma obtained.

Attempt 3: stabilize n by replacing unused vertices with a bounded reservoir and perform exact minimax on isomorphism classes of histories. Even if a finite board bound N(k) is proved, a bound depending on k does not establish a universal c. No amplification gadget proving unbounded difference was found either. For n<2k all k-subsets intersect, so every play claims the entire board and both payoffs are n−k+1. This is a trivial parameter case, not a solution. The n=2k complement-pair description does not control transversal payoff. Park with these concrete gaps; no finite sweep was run.

## 324757: full-field Walsh obstruction remains open in this lane

Read all five pages of arXiv:1212.6553v1 and the six-page published CAI 2013 body supplied by the author. Conjecture 3 lies in the section explicitly assuming characteristic two. MathDB's field-unrestricted wording must not be exploited through odd-characteristic counterexamples. The source already provides a balanced Boolean function in ten variables with exactly one zero Walsh coefficient, and explains how to realize it as Tr(f) for a permutation. Thus eliminating zeros for just lambda=1 is already published and insufficient: the target product ranges over every nonzero lambda and a.

Attempt 1: use Parseval/orthogonality of the Walsh transform of a permutation to force an interior zero. Parseval gives sum_a W_f(a,lambda)^2=q^2 for each lambda, with a=0 zero. It does not force an additional zero once q is large. Attempt 2: preserve the source's zero-free component while completing its balanced fibers to a permutation. There is no control on the other q−2 nonzero components; a single extra zero defeats the construction. Attempt 3: power permutations make all lambda spectra equivalent by Equation (3), but this merely reduces to the famous power-function vanishing conjecture; the source gives divisibility modulo primes, not an exact zero. Park. No floating-point character sums or heuristic zero decisions were used.
