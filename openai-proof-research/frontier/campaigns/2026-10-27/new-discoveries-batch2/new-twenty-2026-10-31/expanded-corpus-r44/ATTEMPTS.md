# r44 mathematical handback — zero proposed credit

All statements in statements.txt were read literally. Only the source contexts identified below were primary-read. No full-scope theorem was closed, and no Lean theorem is proposed. Counts stay 3/20 beyond 39.

## 351027 — first priority, parked with a concrete sign lemma

New primary reading: Wang–Shan–Zhai, arXiv:2106.09238, definitions of A_alpha and B(n,d), diamond core and five attachment types in Section 5, Lemma 5.2 proof reducing types 1/2/3, Theorem 5.1 and its three-case proof reducing maximizers to B3* or B5*, and Theorem 5.3's characteristic-polynomial comparison at alpha=1/2. The latter proof is not a proof for alpha>1/2. Conjecture 5.1 is exactly the selected alpha interval, rather than the published adjacency comparison in Guo2007. Relevant published references in this source were identified, not independently body-read. No later full-alpha theorem was located in the bounded searches; this is not novelty clearance.

Use diamond vertices 0,1,2,3, edges 01,12,23,30,13. B3 has s leaves at 1 and pendant paths of edge lengths a,b at 1,3. Its balanced parameters satisfy a+b=d-1 and s=n-d-3. B5 has s+1 leaves at 1, with balanced paths at 0,2 of total length d-2. All code constructs these actual simple graphs and checks order, n+1 edges and diameter. Domain caution: n=d+2 makes the displayed B3 construction unavailable, whereas B5 can exist. This is a source/parameter admissibility issue to resolve before a full literal endpoint, not a qualifying counterexample. No credit is sought from this boundary defect.

### Attempt 1: exact finite model, then numerical diagnosis

`diagnostics.py` compares the largest eigenvalues at alpha in {0.50001,0.51,0.6,0.75,0.9,0.99}, all 7<=n<=36 and 4<=d<=n-3. Full output has 2790 comparisons, no negative differences. The smallest observed positive difference is around 7.1e-10; no certified sign follows from floating arithmetic. This finite evidence supports continuing an analytic comparison; it proves neither the universal result nor any mathematical novelty.

### Attempt 2: all-length Schur reduction

Write beta=1-alpha. A pendant arm of length j contributes self energy
h1=beta^2/(x-alpha), h_j=beta^2/(x-2alpha-h_(j-1)) for j>=2.
After eliminating leaves and arms, retain the 4x4 matrix with off-diagonal -beta at the diamond edges. For B3 its diagonal is
(x-2alpha, x-alpha(s+4)-s beta^2/(x-alpha)-h_a, x-2alpha, x-4alpha-h_b).
For B5 its diagonal is
(x-3alpha-h_c, x-alpha(s+4)-(s+1)beta^2/(x-alpha), x-3alpha-h_e, x-3alpha).
These formulas assume all arms are nonempty; the short boundary d=3 requires separate treatment.

For d=2l, a=l,b=l-1,c=e=l-1. For d=2l+1, a=b=l,c=l,e=l-1. Put p=h_(l-1), z=x-2alpha-p, q=beta^2/z. Let M3,M5 be those reduced matrices. Dividing the full characteristic-polynomial difference by its common positive tail factor leaves
z det(M3) - (x-alpha) det(M5).
`spectral-schur.py` symbolically expands/factors both parity cases, with full exact output in spectral-schur.log. This is a rational identity computed in SymPy, not a formal proof or a sign certificate. The even numerator factors further by -(alpha+p); both expressions are affine in s. Treating p as an arbitrary positive variable loses essential constraints from the finite-arm recurrence.

Remaining decisive lemma: for every admissible s,l, 1/2<alpha<1, at x=rho_alpha(B5), prove positivity of all eliminated tail denominators and strict negativity of this difference, using the actual recurrence constraints on p. Then det(xI-A_alpha(B3))<0 forces an eigenvalue above x. Also recover all small/admissible source parameters and a formal maximizer-to-two-candidates bridge. No sign proof, formal spectral bridge, or complete source-domain reconciliation was obtained. An alpha=1/2 result, a fixed diameter, or a positivity assumption on this polynomial is not the requested theorem.

## 351663 — second priority, bipartite crumby coloring held

New primary reading: Barát–Blázsik–Damásdi, arXiv:2108.08118, Conjectures 1 and 3, exact vertex-color conditions, Theorem 4's Edmonds–Gallai statement and entire Theorem 5 proof (1-subdivisions of cubic graphs). Also read the original Section 3 introduction and Conjecture 9; these do not assert that the bipartite conjecture was refuted. The record's refuted tag quotes a sentence about the original cubic conjecture and does not settle this ID.

### Attempt 1: transplant the source matching mechanism

In a 1-subdivision, the original vertices are red and subdivision vertices initially blue. A perfect matching of the original cubic graph supplies red subdivision vertices, giving disjoint red P3 components. The source treats missing perfect matchings with Edmonds–Gallai and detailed recoloring. Ordinary cubic bipartite graphs have no distinguished degree-two subdivision vertices, so this proof does not automatically transfer. Its exact scope is already known and not a new solution.

A natural alternative colors one bipartition A entirely red and selects red vertices in B. In a cubic bipartite graph, every selected B vertex has three red neighbors. Avoiding a red simple P4 forces every A vertex to be adjacent to at most one selected B vertex, and avoiding isolated reds forces exactly one. Thus selected neighborhoods must partition A, in particular 3 divides |A|. The cube has |A|=4, so this strategy cannot prove the general statement. The cube itself is not a counterexample: other colorings exist.

### Attempt 2: structural reformulation and recoloring

A connected bipartite graph of maximum degree at most three with no simple three-edge path and at least one edge is a star K1,t with 1<=t<=3. Indeed, a longest path has at most two edges; any additional neighbor of a leaf of a length-two path would create a three-edge path, unless it joins the other endpoint, which would make a triangle. Connectivity therefore places all vertices at one center. Consequently the exact task is to find an induced nontrivial star forest whose complement induces only isolated vertices and edges. This reformulation preserves the original coloring semantics.

A maximum-cut coloring of a subcubic graph makes every vertex have at most one same-color neighbor: otherwise flipping that vertex increases the cut. This supplies small monochromatic components but can leave isolated red vertices. Flipping an isolated red vertex blue can create blue degree three. Recoloring a blue neighbor red may join red components into a forbidden P4; no globally decreasing potential eliminating these defects was found. The bipartite star-forest equivalence alone does not close this repair lemma.

### Attempt 3: bounded exact-color diagnostics

`diagnostics.py` takes a fixed seed and 30 unions of three permutation matchings for each balanced part size 4,5,6,7,8; parallel edges collapse, yielding 150 explicitly recorded simple bipartite subcubic graphs (not necessarily cubic, connected, distinct, or exhaustive). It exhausts vertex-color masks only until it finds a valid coloring and checks red neighbor conditions, blue degree and every simple red P4. All 150 have a coloring; edges and masks are retained. These exact finite computations remain diagnostics, without a Lean soundness bridge.

Remaining lemma: a terminating defect-repair operation, or a complete obstruction proof for an induced star forest with matching complement, for all finite bipartite subcubic graphs. A general matching decomposition including all cubic components and cut structures is missing. No counterexample, universal proof, or Lean endpoint exists here. Pintér2607.06515 settles only the outerplanar class (separate ID351664); its proof explicitly identifies the bipartite case as a remaining direction. Do not widen its finite grammar to arbitrary bipartite graphs.

## 351300 — third route, full game semantics still unresolved

New primary reading: Clarke–Finbow–Messinger–Porter2107.07368, full move/observation rules, the small-common-neighborhood definition, Observation9, Theorems10–12 with proofs, and Conjecture20. Important literal-source discrepancy: Upsilon is the MINIMUM cardinality of a nonempty S with |intersection N(v)|<=|S|, not the raw record's 'maximum size'. Use source scope; changing the raw word is not a discovery.

The source proves the Upsilon(G)+Upsilon(J) bound by placing cops on minimum sets in both factors, then simultaneously covering the two invisible candidate sets in one move. This proves the requested formula whenever each cH is at least its Upsilon. A route through cH(X)>=Upsilon(X) for every connected X would suffice, but no such lower bound was proved. A winning strategy can use information accumulated in previous rounds; the initial cardinality of an invisible set alone does not prove this bound.

`hyperopic.py` implements a finite imperfect-information reachability diagnostic. A state is a multiset C of cop locations and a belief B of possible robber vertices; observations partition post-move beliefs into one invisible set and visible singletons. Cop actions first remove captured positions, then the robber takes a closed-neighborhood move, then observations partition. A hyperedge wins if every successor observation state wins; least-fixed-point backward reachability handles eventual finite capture. This is a Python model, not a certified semantics theorem.

For all 31 connected unlabeled simple graphs on at most five vertices (canonicalized by permutations), the computed cH is >=Upsilon. Therefore every join of two such factors is ALREADY covered by source Theorem10, and the script intentionally runs no nontrivial join computation. This is not a check of new mixed-minimum cases. The 31 factor diagnostics and their cH values are retained; no completeness beyond this finite graph inventory and unformalized model is claimed.

Trying to run independent factor strategies fails at the exact information step: an invisible robber may lie in either factor. A cop group cannot assume that the robber is confined to its own factor while the other group moves. To close the general case one needs a belief-state invariant that either confines the robber, forces visibility while each factor retains a cop, or decreases a well-founded rank for all possible hidden positions. Neither independent ordinary winning strategies nor Theorem10 supplies this invariant. Park rather than promote this strategy outline as a proof.

## Other primary-body dispositions

- 351026: Liu–Diwan–Zhang2512.22761 Theorem3.1 and Corollary3.2, including full induction proof, give the exact all-graph forcing bound. Their k=n-F(G) substitution is literal. Exclude public prior proof; do not formalize for credit.
- 351322: Bora–Choi–Tang institutional manuscript Theorem1.1 gives exactly the even/odd formula; read its concluding proof and the original Li Conjecture3.4 context. Published Discrete Mathematics348(2)(2025)114257 is a separate version; publisher search identified Theorem3.26, not a body-read of that version. The institutional theorem and proof are enough to stop rediscovery; not all its auxiliary case lemmas or computational base cases were audited.
- 351252: full primary note2107.04998 was read. On a snark of order2r, ex(G,rK2)=|E|-3 whereas any two perfect matchings intersect, so its matching Kneser graph is edgeless and chi=1 rather than3. This is the paper's explicit prior refutation, irrespective of metadata contradictions. No independent replay of cited Schönberger theorem is claimed.
- 351664: Pintér2607.06515 Theorem1.1, definitions of admissible boundary states, Section4 induction and Section5 full main proof were read. Finite closure certificate replay and all grammar proofs were not independently audited. It is an exact public full-scope proof claim, sufficient for no discovery credit; not an independent certification of its computer-assisted proof.
- 351537: source Conjecture1 does NOT state the raw iff planar/max-degree-four assertion. It states a 3-semi-transitive claim for Delta<=4 and a sufficient condition involving non-word-representable planar G. A nonplanar 3-edge-colorable example against the raw iff would only attack a defective paraphrase. Stop for source-fidelity mismatch, without solving an adjacent source clause.
- 351574: source explicitly defines the imprimitive action on V times {1,...,n}, whereas the record calls it product action. Read Lemma4.1 and Proposition4.4's proof and Conjecture4.6. These supply bounds only for the specified action. No novelty or solution from changing actions is claimed; park the semantic qualification before any large group search.
- 350817/350818: read actual Conjectures6.3/6.7 and conditional Lemmas6.4–6.6 proofs in2105.13357. The safe-gluing definition and full toric-ideal classification machinery were not audited. Complete-DAG/decomposition degeneracies and nonexistence of separating sets are not qualifying solutions. No classification attempt is claimed.
- 351662: original source explicitly reports prior counterexamples. The historical scout r285 also excludes the original refuted family and a vague relaxation. Retain that old exclusion and stop. Counterexample construction bodies were NOT read in this pass; the report is inherited/source-attested rather than an independent refutation proof.

The remaining 28 IDs have literal/metadata/history review only; their source definitions and proof bodies are unreviewed here. None is declared known, new, false, or technically exhausted.
