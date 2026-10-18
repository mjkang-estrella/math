# T118S: higher-level configuration gaps via local stock splitting

Author-side theorem and proof; TECHNICAL / NO NOMINEE. This is not an independent review. The unchanged statement and precise SA indexing convention are frozen in original-scope.txt. No quantitative number-of-rounds claim as a function of item count is made.

For every pair of integers r,c≥0 there is a rational bin-packing instance I with exactly 5B indexed items, all larger than 1/6, whose individual-copy configuration relaxation after r Sherali–Adams rounds has value B, whereas OPT(I)>B+c. Every feasible physical-copy subset is a variable, not merely the configurations used below.

## 1. Dependencies and conventions

The pinned manuscript *Additive hardness and unbounded configuration gaps in bin packing*, at fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, supplies thm:reduction, lem:encoding, the physical inventories in instance.tex, and prop:completeness with its full local construction in completeness.tex. These are stipulated source results. Its prop:fractional only supplies ordinary LP first moments for K4; it does not state the present hierarchy theorem.

Schoenebeck, *Linear Level Lasserre Lower Bounds for Certain k-CSPs*, full version LasserreNew.pdf, Theorem12, Claims6–7, and the FGLSS construction in Corollary15 supply the primary antecedent. Precisely, for any fixed integer t there is a finite 3-XOR system F with M clauses, each on three distinct variables, such that (a) every full assignment satisfies at most 5M/8 clauses; (b) there are consistent probability distributions μ_S on all variable subsets S of size at most t; and (c) μ_S is supported on assignments satisfying every clause whose three variables lie in S. Take δ=1/8, fixed sufficiently large density and underlying variable count in Theorem12, then use Claims6–7. The actual primary theorem gives much larger t; only this finite-t contract is used. No need to reproduce its Lasserre lower-bound proof. We derive the exact per-clause identity below, rather than assuming objective equality implies all conditioned identities.

The target's SA_r functional is defined through degree r+1. Literal products through that degree must have nonnegative expectation; covering constraints multiplied by literal products of degree at most r must have nonnegative expectation. All products are Boolean-multilinearized. We construct equality for every multiplied covering constraint. Choose the primary local-distribution order

    t = 6(r+1).

## 2. Exact local cover states

Construct the FGLSS conflict graph G. There are four vertices (C,a) for each clause C, one for each satisfying assignment a of its three variables. Two distinct vertices are adjacent exactly when their partial assignments disagree on a shared variable. In particular the four vertices in each clause form a clique. Repeated clauses cause no difficulty: their clause indices remain distinct. Write n=4M and k=3M.

Every independent set consists of mutually compatible partial assignments, hence extends to a full assignment satisfying every represented clause. It contains at most one vertex from each clause. Therefore α(G)≤5M/8 and

    τ(G) = n−α(G) ≥ 27M/8.

For an assignment z on the variables of clause C define the cover bit

    x_(C,a)(z) = 1 − 1{z restricted to C equals a}.

Whenever C is satisfied, exactly one of its four vertices has cover bit0 and the other three have bit1. Thus the sum of the four cover bits is EXACTLY3 on every assignment in the relevant local distribution. On any edge uv, the labels at u and v are inconsistent, so no assignment to their union of variables makes both cover bits0. The cover constraint is consequently a pointwise identity of supports on at most six original variables. Both properties persist after conditioning on any additional variables within the t-variable budget, by consistency and clause support. No inference from mere unconditioned mean cardinality is used.

Apply the pinned graph-to-packing construction to (G,k) with the desired c and fixed ρ=1/32. Its soundness gives

    OPT(I)≤B+c ⇒ τ(G)≤k+ρn=25M/8,

contradicting τ(G)≥27M/8. This establishes the integral lower bound for the full set of feasible bin configurations. All subsequent work constructs the hierarchy witness for precisely this same source instance.

## 3. Localizing physical pooled inventories

Use all original indexed physical copies, without changing their sizes or introducing capacities, forbidden bins or marked constraints. Species and labels here are only proof metadata. The five disjoint source roles are X (row), A (anchor), U (global auxiliary), D (local auxiliary), and F (flag). Every intended bin has one item of each role.

For each graph vertex v, fix all choices in the source local completeness construction twice, once in state x_v=1 (selected) and once in state x_v=0 (unselected): fixed funded root rows, fixed separate tree marking, fixed placement of unused positive local auxiliaries and zeros, and a deterministic tie-breaking rule for the sorted completion/deadline matching. Leave U and F slots as species placeholders at this stage. The resulting M templates depend only on x_v. The remaining rows at every incidence position are the short rows when selected and long rows when unselected. Pair them with that position's keys by the fixed ordinal among its d copies. Assign D_G copies by incidence position and ordinal. This makes each G row slot local to its one incident graph edge.

As in the source, vertex v has t_(v,+)+J_v plus-global slots, t_(v,−) minus-global slots, and t_v+2J_v total bins. It needs d length-one U+ copies when selected and none otherwise, and d length-one U− copies when unselected and none otherwise. The other slots use length-zero copies of their indicated side.

Partition the actual global pools into fixed clause blocks, once and for all. For the four graph vertices V_C of clause C, set

    A_C = Σ_(v∈V_C)(t_(v,+)+J_v),    D_C = Σ_(v∈V_C)t_(v,−).

Give that block exactly 3d U+ copies of length1, A_C−3d U+ copies of length0, d U− copies of length1, and D_C−d U− copies of length0. All these integers are nonnegative: each of the four vertices has at least d root slots on each side. Their sums over clauses are exactly the source stocks, since k=3M and n−k=M. Thus they really partition the existing physical pools. Within each block and each species, assign its copies in a fixed order to the required slots in a fixed order. The number of required slots equals the assigned stock for every satisfying assignment of that clause, because exactly three cover vertices are selected. This entire assignment depends on only the three variables of C.

Partition each flag pool by vertex: t_v copies of F_T, J_v of F_M, and J_v of F_G. Allocate F_T by tree-row index and allocate F_M and F_G by incidence position and ordinal. These numbers do not depend on selection. This exhausts the flags and makes their locations deterministic once the relevant row state is known.

For each graph edge uv retain its own dR permits and dR nonpermits. If one endpoint is unselected, give all permits to that endpoint's G slots and all nonpermits to the other endpoint's G slots. If both are selected, choose the smaller vertex label for the permits. The case of two unselected endpoints cannot occur on an assignment to the union of the two clause variable sets. Match physical copies in fixed orders to the dR slots at each endpoint. Long rows receive permits; short rows may receive either species. Source eq:exact-edge-completeness proves feasibility. This assignment depends on at most six original variables.

Every M bin is feasible by the already-proved source local completion/deadline argument. Replacing a placeholder by any physical copy of its assigned species does not change size. Every G bin is feasible by its just-described endpoint rule. Each physical X-row is used exactly once in the source local construction, either in M or in G; use that unique row as the permanent name of its bin slot. This avoids ambiguous multiple active origins for a configuration.

## 4. Local configuration indicators and conservation

For each physical row b, its tuple is a deterministic function of at most six original XOR variables: a tree row needs its own clause; a job row needs its own clause and the clause of the other endpoint of its fixed graph edge. M/G switching only changes that row slot's remaining items. Use a branch-local convention for invalid inputs: an M tuple is active whenever its OWN clause is satisfied and its own state selects that M row; do not inspect any neighboring clause. A G tuple is active only when BOTH endpoint clauses are satisfied and its endpoint state selects that G row. Otherwise that branch is inactive. This extension makes the indicator functions total Boolean functions and cannot affect any local expectation used below. In particular an M configuration indicator depends on only its own clause even when the same physical job row has a possible G use on an edge. Imposing an unnecessary neighbor-clause guard on M bins would destroy the bounded item-neighborhood claim below, so that guard is expressly absent.

For every feasible subset H, define f_H(z) to be1 exactly when the row contained in H has active tuple equal to H. If H has other than five items, does not have exactly one row, or is never generated by a row slot, define f_H=0. The disjoint roles ensure that H cannot have two candidate row origins. Thus f_H is a well-defined Boolean function depending on at most six XOR variables, even if its tuple happens to agree across several local states. Distinct numerical size coincidences do not identify physical copies and cause no ambiguity.

We need more than bounded dependence for each f_H: each item equality must also be local. This follows from the explicit allocation:

* A tree row, deadline anchor, D_M copy, F_T or F_M copy, and every clause-block U+ or U− copy has all its possible uses inside its own clause's M construction, except that a job row may instead enter its own edge's G bin.
* A job row, key, D_G copy, F_G copy, or W auxiliary has all its possible G uses at one fixed graph edge. A job row's alternative M use stays at its own endpoint, whose clause is already in that edge neighborhood.

Consequently, for each physical item i, there is a set T_i of at most six XOR variables such that every nonzero f_H with i∈H depends only on T_i. For M-only items one may use the three-variable clause set; for the edge-listed items use the union of the endpoint clauses. On every assignment to T_i satisfying those one or two clauses, the construction consumes item i exactly once. Indeed local X/A/D inventories are partitioned by the two-state source construction; block U copies are bijectively assigned to exactly matching slot counts; flags are assigned to distinct fixed slots; and each edge pool is bijectively assigned to its two endpoint sets of G slots. We therefore have the pointwise local conservation identity

    Σ_(H∋i) f_H(z) = 1

on the support of μ_(T_i), and also on every larger local law containing T_i. The summation is over ALL feasible subsets, with unused subsets assigned the zero function. The possibly large number of summands does not enlarge the variable neighborhood T_i.

## 5. Sherali–Adams witness

For a set A of at most r+1 distinct configuration variables define

    L(∏_(H∈A)y_H) = E_(μ_S)[∏_(H∈A) f_H],

where S is the union of their variable neighborhoods. Then |S|≤6(r+1)=t. Any unused extra variables can be integrated out; consistency makes the definition independent of the chosen superset. Extend linearly to multilinear polynomials.

L(1)=1. For every product of at most r+1 configuration literals, its L-value equals the expectation of the same product of Boolean f_H literals in a single actual local probability space. It is nonnegative. This includes all bounds and every negative-literal condition, not just positive moments.

Fix an item i and a product P of at most r configuration literals. The union of the neighborhoods involved in P and T_i has size at most6r+6=t. Consistency puts every term in L[P(Σ_(H∋i)y_H−1)] in that single local probability space. The item-conservation identity from §4 is pointwise on its support. Hence

    L[P(Σ_(H∋i)y_H−1)] = 0.

Boolean multilinearization is valid because every f_H is Boolean. Thus L is feasible for the precise SA_r relaxation in original-scope.txt and even satisfies every lifted covering equality.

Only five-item configurations have nonzero first moments. Sum the unmultiplied item equalities over all 5B items to obtain

    5 Σ_H L(y_H) = 5B.

The witness objective is B. Conversely every feasible first-moment solution has nonnegative entries, covers all5B items, and every feasible bin has cardinality at most5 because all item sizes exceed1/6. Summing coverage therefore forces Σ_H L(y_H)≥B. This proves SA_r(I)=B, completing the unchanged full statement.

## 6. Contribution and limits

This argument initially appeared to require a global consistent injection of pooled copies. The FGLSS per-clause exact count removes that issue: a fixed partition of identical-copy stocks makes every configuration and conservation identity local. The resulting lift is the ordinary bounded-junta substitution already isolated by Schoenebeck's Lemma16, with a direct SA verification above. Source118 already supplies the nonroutine scalar encoding, competing trees, arbitrary-packing extraction and additive amplification. Schoenebeck already supplies high-level local satisfiability, the conflict graph and its cover gap. The remaining stock split and deterministic assignments are routine bookkeeping at these contracts.

Accordingly the author disposition is TECHNICAL / NO NOMINEE, not a claim that this exact theorem appears verbatim in the literature. No proof or contribution gate has run. No global novelty or priority claim is made. The root's independent author reading of source completeness and its unique-row indexing observation are recorded as author assistance, not as independent review. The result neither changes the frozen statement nor asserts a stronger Lasserre conclusion, machine-indexed scheduling gap, quantitative hierarchy rank, or type-configuration hierarchy theorem.
