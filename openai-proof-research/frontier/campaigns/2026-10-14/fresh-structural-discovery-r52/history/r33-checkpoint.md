# Structural r33: orientation-compatible cycle decomposition

Status: **full target unresolved; no nomination or count increment**. The local lemmas below are author-level technical deductions, with explicit source antecedents. They have not received independent proof or contribution review. No narrower theorem replaces the target.

## Fixed research question

Does there exist an absolute constant C such that every finite digraph D=(V,A), with no loops and at most one arc per ordered pair, satisfying d⁺(v)=d⁻(v) for every v, has an arc partition into at most C|V| directed simple cycles? Antiparallel pairs are allowed; their directed two-cycles count as cycles. Isolated vertices and disconnected balanced graphs are allowed. The empty partition handles A=∅.

This is the full directed linear-cycle-decomposition question, not an assertion about dense, bounded-degree, quasirandom, or specially oriented graphs. It was communicated to the parent before the local work. The question has remained unchanged; there is no full-proof freeze or candidate acceptance. A balanced weak component with an arc is strongly connected: the condensation has balanced total inflow/outflow at every vertex, so a source component has no outgoing arcs either, and removing it proves that the condensation has no edges.

The undirected input is stipulated family181 at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb. Its `thm:main` supplies Cn undirected cycles and edges; `cor:eulerian-cycles` already includes the ordinary undirected Eulerian and weakly quasirandom consequences. Those are not new results. The primary KLMN paper, arXiv:1911.07778v2, Theorem1.8, gives O(n log Δ) for the directed question. Its Lemma2.2 proof exhibits the exact harmonic accounting ∑v H_{d⁺(v)}. The Ai–Gutin–He–Yeo 2025 note, arXiv:2510.26426v1, introduction and Theorem1.4, still cites the KLMN degree-dependent bound, and improves a different cycle-length bound to sqrt(2d)−3/2. The weighted-conjecture wording in that note's displayed introduction is not imported as a theorem or used in our argument. The bounded searches did not establish a stronger full directed decomposition bound; this is not a worldwide completeness claim.

## Positive local operation: folding without destroying balance

The source's `lem:pair-folding` deletes loops and repeated edges after identifying pairs. Those deletions do not preserve a directed degree-balance invariant. Keeping every arc and subdividing the exceptional ones repairs that particular problem.

**Lemma F (technical balanced folding).** Let J be a loopless simple digraph, allowing antiparallel arcs, and let X₁,…,X_t be pairwise disjoint vertex sets. Suppose a≥1, m_i=|X_i|≥max(8,16a²), every vertex of their union has total incident degree d⁺+d⁻≤a, and every vertex v has at most a incident arcs whose other endpoint belongs to X_i, for each i. Then pairings inside the X_i, leaving exactly m_i mod2 unpaired, yield a simple loopless directed subdivision Q of the full identified multigraph, with

|V(Q)| ≤ |V(J)| − (1/3)∑i m_i.

Every original arc is represented by one directed arc or a directed two-arc path with a private new internal vertex. If J is balanced, Q is balanced. The representation uses every original arc, with no deletions.

**Proof.** Choose independent uniform pairings, with the source's dummy-vertex convention for odd m_i. Let Z count original arcs becoming loops plus unordered pairs of distinct original arcs that become the same ordered nonloop arc. The source's pairing probabilities apply unchanged. We spell out why the presence of opposite arcs does not invalidate the estimates.

An internal arc becomes a loop with probability at most 1/(m_i−1). There are at most am_i/2 internal arcs. For a common-endpoint collision the other two distinct endpoints must be paired; the arcs must have the same incidence orientation at the common vertex. Counting all pairs of incident arcs only enlarges this set. If d_i(v) denotes incident arcs toward X_i, then ∑v d_i(v)=∑x∈X_i(d⁺(x)+d⁻(x))≤am_i and d_i(v)≤a. Thus loops and common-endpoint collisions have expectation at most ∑i a²m_i/[2(m_i−1)]≤(4/7)∑i a². Two antiparallel arcs with the same two endpoints cannot become the same ordered nonloop arc; if their endpoints are identified they are already charged as loops.

For four distinct endpoints, two identifications are required. If both pairs lie in one X_i, there are at most e_i²/2 pairs of internal arcs, e_i≤am_i/2, and at most two possible pairing patterns. The expectation is at most ∑i a²m_i²/[4(m_i−1)(m_i−3)]≤(16/35)∑i a². If the paired fibers lie in X_i and X_j, write e_ij for the total number of arcs between them, in both directions. There is only one allowed pairing pattern; ignoring the necessary common orientation is an upper bound. Independence gives at most ∑i<j e_ij²/[2(m_i−1)(m_j−1)]≤(16/49)∑i a², using e_ij≤am_j and ∑j≠i e_ij≤am_i exactly as in the source. These cases exhaust all collisions. Consequently

E Z ≤ (332/245)∑i a².

Choose a pairing with Z no larger than its expectation. Keep every arc in the identified directed multigraph. Subdivide each loop once with a fresh vertex, and subdivide all but one arc in every ordered nonloop parallel class, using a different fresh vertex each time. This produces a loopless simple digraph, including when opposite arcs are present. The number P of added vertices is at most Z, since a parallel class of size s contributes s−1≤binom(s,2). Identification preserves degree balance by summation over a fiber; a loop contributes equally to in- and out-degree. Subdivision preserves old balances and gives degree (1,1) at each new vertex.

Writing S=∑i m_i, the new order is |V(J)|−∑i floor(m_i/2)+P. Since m_i≥8, floor(m_i/2)≥7m_i/16. Since m_i≥16a², P≤(83/980)S. The net saving is at least (7/16−83/980)S=(1383/3920)S>S/3. All claims follow. ∎

This is a source-paid collision calculation plus ordinary subdivision. It is not nominated as substantial. The source's a=D^.01 and minimum active-set order D^.03 satisfy m_i≥16a² at sufficiently large D, so the saving is compatible with its exponent choices. This observation does not supply balanced active batches.

**Lifting interface.** In any directed simple cycle of Q, suppress the added subdivision vertices. The remaining quotient fibers are distinct, except for the closing visit; a subdivided loop gives a cycle with just one such fiber. Each original representative arc has the specified direction. At a fiber entered at u and exited at v with u≠v, request a directed u→v path in the reserved router. For a subdivided loop arising from an original arc x→y, this request is y→x. Forbid internally every original endpoint on that quotient cycle, and put all requests of the same cycle in the same team. If routers occupy disjoint vertex sets and the directed routing lemma in `directed-routing.md` applies, the paths and representatives give one directed simple cycle per quotient cycle, even for the one-fiber case. The latter has at least two arcs because the original graph had no loops. Each request endpoint uses a distinct incident original arc, so the endpoint load is at most the original incident degree. This is the source's `lem:batch-resolution` simplicity argument with ordered paths, not a full new induction.

## Exact barriers to transferring the remaining operations

**B1: splitting undirected pieces into directed runs has quadratic cost.** Let m≥2 be even, N=2m, A={a_j:j∈Z/N}, B={b_j:j∈Z/N}. Decompose K_{N,N} into m undirected Hamilton cycles H_i: H_i is the union of the two perfect matchings a_j b_{j+2i} and a_j b_{j+2i+1}, for 0≤i<m. These are Hamilton cycles because walking successively through the two matchings translates the A-index by one. The matchings partition all shifts, so the H_i partition all edges.

Orient every edge in H_i from A to B when i<m/2, and from B to A otherwise. The resulting oriented graph has in-degree and out-degree m at every vertex. It is in the fixed full target. Yet inside any given H_i no directed path has more than one edge. Thus splitting this perfectly good undirected m-piece decomposition into directed runs produces 4m²=n²/4 pieces, where n=4m. This refutes a bounded run-cost transfer from the supplied undirected partition. It does not refute a different global recombination or the full linear conjecture.

**B2: an expanding directed piece can have quadratic imbalance.** Take four vertex classes A₁,B₂,A₂,B₁ of size t, t≥1. First put all forward arcs along that cyclic order, including B₁→A₁. This directed four-part blowup D₀ is balanced. Add all arcs A₁→B₁ and A₂→B₂ to obtain P_t. No ordered parallel arc or loop is present; antiparallel pairs are allowed. Every A-vertex has excess d⁺−d⁻=t, and every B-vertex has excess −t.

Both directed cut boundaries of P_t have size at least (t/2)min(|S|,4t−|S|). Indeed it suffices to prove this for D₀. For s=|S|≤2t and class counts x₁,x₂,x₃,x₄, its outgoing boundary is ts−∑cyclic x_i x_{i+1}. The sum equals (x₁+x₃)(x₂+x₄)≤s²/4≤ts/2. Thus the outgoing boundary is at least ts/2. Balance of D₀ equates its incoming and outgoing boundaries, and complements handle s>2t. Adding arcs cannot lower either boundary.

Suppose P_t is partitioned into directed cycles, single arcs, and residual graphs whose union of vertex supports is R with |R|≤t/2. Each vertex outside R receives no residual arcs. Directed cycles contribute zero excess there. At least 2t−|R|≥3t/2 of the A-vertices lie outside R, each with excess t. Summing their positive excess forces at least (3/2)t² single-arc parts, because one arc contributes at most one to that sum. Consequently the literal directed analogue of the source's arbitrary-graph `lem:small-residue`, with O(r) completed cycles/edges and residual order≤r/8, is false, even under two-sided cut expansion linear in r=4t.

This is not a counterexample to the full Eulerian target: P_t is unbalanced. It is an explicit obstruction to a required operation on arbitrary assigned pieces. It occurs as an arc subset of the balanced symmetric complete bipartite digraph between A₁∪A₂ and B₁∪B₂; adding B₁→A₂ and B₂→A₁ supplies exactly its missing balance. Thus starting with a balanced input does not make arbitrary edge assignments balanced.

**B3: the local route itself is not the missing step.** `directed-routing.md` proves the technical two-sided-expansion routing interface by retaining forward/backward labels and choosing one common direction among the obstructed roots. Its cut-growth operation is the source's proof. Strong routing plus balance-preserving folding does not pay the false arbitrary-piece small-residue assertion B2.

The classical K₄ symmetric-digraph obstruction is also retained as a control: three undirected Hamilton cycles partition its doubled underlying multigraph, whereas its directed cycle number is four (KLMN introduction credits Dean). The exact enumerator checks this finite statement, but it is not new research. Antiparallel arcs cannot simply be removed as separate two-cycles: there can be Θ(n²) such pairs.

## Unpaid interface and next mathematical step

A viable continuation must construct the scale pieces together with directed balance/endpoint accounting. In particular, it needs either (i) balanced recursive pieces with a total vertex-saving inequality and usable two-sided routers, or (ii) a controlled defect budget whose total positive imbalance is linear in the saved vertex mass, and whose later repair leaves enough router expansion. Arbitrary color classes, arbitrary edge boxes, and a bound on undirected degree alone do not supply either condition. The source's `lem:scale-split` explicitly assigns all edges to overlapping boxes and its `lem:small-residue` assigns each nonreserved edge to an arbitrary reservoir complement; neither statement contains this directed invariant.

Even the routing and folding results above are conditional local steps. They do not prove the required global balanced splitting, do not remove the harmonic loss in KLMN, and do not establish a new long-cycle theorem by averaging. The unchanged full target remains unresolved.

## Formal interface, validation, and contribution limits

A feasible honest Lean fragment would encode finite directed arc sets, prove cut-balance by double counting, prove that identification and private subdivision preserve incidence balance, and certify the rational folding savings and four-class cut polynomial. The all-graph decomposition, hypergraph matching, random-pairing estimates, directed routing, and literature contribution would remain human arguments. No Lean implementation or formal-coverage claim is made for this unresolved checkpoint.

`checks.py` verifies the explicit directed and undirected finite constructions, the class-count cut inequality, the folding rational constants, and K₄ cycle enumeration using exact integers/Fractions. These are diagnostic controls, not a general proof. `verify.py` binds the complete owned inventory to a caller-supplied manifest SHA256, validates pinned Git blob identities, reruns diagnostics, and rejects a wrong anchor. Integrity is not mathematical validity or novelty.

Only the assigned r33 directory was written. There were no nested agents, shared ledger edits, commits, uploads, or publication actions. Original prose is attributed to Myeongjin Kang, no affiliation, under CC BY4.0; original code is MIT. Private third-party source bodies retain their own rights and are not a public release.
