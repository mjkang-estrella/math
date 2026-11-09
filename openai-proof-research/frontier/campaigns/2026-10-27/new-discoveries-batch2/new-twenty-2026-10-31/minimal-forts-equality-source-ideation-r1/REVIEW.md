# MathDB 372043 — ordinary investigation, credit 0

The full all-graph statement remains unproved here. No counterexample, mathematical search, formal execution, Lean, or child work was performed. The substantive additional conclusions are a triangle-padding implication and a pendant-leaf reduction, proved below. They locate the obstruction more sharply but do not resolve it. Park; no Pi dispatch or finite-search plan is justified by this investigation.

## Scope and source gate

The literal JSON and JSONL agree with target-provenance.json on MathDB 372043 and its UUID. The precise target is: for every finite simple unweighted graph G, if the family of ALL inclusion-minimal nonempty forts has cardinality |V(G)|/3, then its ordinary zero forcing number is |V(G)|/3. There is no connectedness, positive minimum degree, or isolate exclusion. v1, lines 79–84, defines the ambient class as all finite simple unweighted graphs; v1 Conjecture 6.3, lines 1127–1136, has that ambient class. The zero-vertex graph, if admitted, has no nonempty forts and zero forcing number zero, and satisfies the claim trivially.

The original source is Cameron–Li, On the minimal forts of trees, arXiv:2512.12874v1, 14 December 2025. It explicitly states the all-graph implication as Conjecture 6.3. Propositions 5.1, 5.2 and 5.4 give the known transversal/packing consequences. v2 (8 March 2026) and v3 (11 March 2026) instead prove tree equality in Theorem 5.4 and retain the general lower bound only as a conjecture in the conclusion. Their omission of Conjecture 6.3 provides no explanation for its removal and no all-graph resolution. The inspected current arXiv landing page still identifies v3; no journal-reference field or later correction is advertised there. This is a bounded observation, not proof that no journal or correction exists elsewhere.

Abiad–Ghasemi Nezhad, Fort Abundance in Zero Forcing, arXiv:2609.11754v1 (10 September 2026), Lemma 2.2 proves component additivity. The full inspected Section 2, lines 81–410, proves the lower bound for block graphs in Theorem 2.8, not arbitrary graphs or the required global equality rigidity. Its other main counts concern arbitrary forts/compatible collections, not the family size at issue. Its cited Nguyen–Kenter paper arXiv:2605.07298v1 was checked at current abstract/version depth only: the announced theorem is an upper extremal count for trees. No proof-body clearance is claimed for that paper or its predecessors. We do not rely on v1's claimed Eulerian theorem, whose construction uses vertex sums of cycles rather than an arbitrary cyclic graph.

Primary PDFs/texts are the frozen, read-only r328 copies; exact hashes and retrieval URLs are in frozen-before.json and r328/http-receipts.json. Newly retrieved metadata and public registry bytes have their own URL/time/hash receipts in this lane. No source figures were visually inspected; no pictured graph is used as a certificate.

## Actual zero forcing and the known reduction

At each step the colored set B may gain v only when a vertex u in B has exactly the one white neighbor v. A process consists of finitely many such steps. If a nonempty fort F is disjoint from the initial B, consider a hypothetical first force into F. Its forcing vertex is outside F and would have exactly one neighbor in F, contradicting the fort condition. Thus no legal process colors all of F.

Conversely, greedily perform any available legal force until none is available; finiteness guarantees termination. If the remaining white set W is nonempty, every colored vertex has zero or at least two neighbors in W, so W is a fort. Every nonempty fort contains an inclusion-minimal fort by finite descent. Hence an initial set meeting every minimal fort cannot stop with white vertices. This proves zero forcing sets are exactly transversals of the full minimal-fort family, with actual process semantics, and Z(G)=tau(F_G).

For any finite family of m nonempty sets, choosing one element per member gives tau<=m. If two members intersect, choose one element from their intersection and one per remaining member to obtain tau<=m-1. If the members are pairwise disjoint, any transversal needs at least m elements. Therefore tau=m iff all members are pairwise disjoint (also for the empty family). This is known substance, not a new result. At n=3m the exact residual is that ALL minimal forts must be pairwise disjoint.

## Component mechanism, with no sign assumption

For components C_i, any fort meeting C_i restricts to a nonempty fort there: neighborhood tests within C_i are unchanged. If a minimal fort met two components, either nonempty restriction, itself a fort of the whole graph, would be a proper subfort. Conversely a minimal fort of C_i remains minimal in the union. Thus the minimal-fort families are the disjoint union of the component families and m(G)=sum m(C_i). This is already companion Lemma 2.2.

Restrict a successful forcing sequence to each component: every retained step is legal, since no vertex has neighbors in a different component. Conversely concatenate component sequences. Minimum cardinalities therefore add: Z(G)=sum Z(C_i). With Delta(G)=3m(G)-n(G) and e(G)=m(G)-Z(G), both quantities are additive, and e>=0 by the known transversal argument. The equality target says Delta=0 implies e=0. It does NOT justify Delta(C_i)>=0.

A useful exact implication is that the full disconnected equality conjecture IMPLIES the universal lower-bound conjecture. Suppose H has Delta(H)=-d<0. A triangle has exactly its three vertex pairs as minimal forts: a singleton fails at a neighbor, every pair is a fort, and the full triple contains pairs. Its zero forcing number is exactly 2: one colored vertex has two white neighbors and cannot start; two colored vertices force the third. Hence Delta(K3)=6 and e(K3)=1.

Take G to be the disjoint union of six copies of H and d triangles. Then

    Delta(G)=6(-d)+6d=0,
    e(G)=6e(H)+d>0.

Consequently m(G)=n(G)/3 but Z(G)<m(G). This is a full conditional construction with complete minimal-fort families accounted for by the component theorem, not an actual witness: no H with negative Delta is known here. It shows that finding a negative component would already refute the source's lower-bound conjecture and, through this padding, the assigned equality conjecture. The prior component comment cannot be repaired by silently assuming the lower bound.

If universal Delta>=0 were available, Delta(G)=0 would force every component tight. The equality claim would then reduce to connected tight graphs. Thus the full target is equivalent to the conjunction of (i) the universal lower bound and (ii) equality rigidity for connected tight graphs. Neither is established by the read source for arbitrary graphs.

## Structural pendant-leaf reduction

This is a handwritten extension of the lifting mechanism in companion Lemma 2.4, not a claimed new theorem of literature.

Let u have p>=2 pendant neighbors x_1,...,x_p, and put H=G-{u,x_1,...,x_p}. H need not be connected. Let b count those minimal forts A of H for which |N_G(u) intersect A|=1. Then

    m(G) >= m(H) + binom(p,2) + (p-1)b.                 (1)

Every pair of the x_i is a minimal fort: only u can see either selected leaf, sees two, and neither singleton is a fort. For each minimal fort A of H with k=|N_G(u) intersect A| !=1, A itself is a minimal fort of G. For k=1, each A union {x_i} is a minimal fort of G. To check the last assertion, outside vertices in H have the same selected neighbors as for A, u sees two, and other leaves see zero. Any subfort avoiding x_i lies in A and would be a fort of H, hence equals A, which fails the test at u. Any subfort containing x_i must meet H (otherwise u sees one); its intersection with H is a fort of H and therefore all of A. These constructions are mutually distinct, including across components of H, proving (1) without assuming they exhaust all forts.

In particular, for p=2,

    Delta(G) >= Delta(H)+3b.                          (2)

If p=2 and b=0, we can prove completeness, giving an exact family formula:

    F_G = F_H union {{x_1,x_2}}.                      (3)

A minimal fort cannot contain u: then every pendant leaf must also belong to it, because an omitted leaf would have its unique neighbor u in the fort; but the fort would then properly contain a pendant-leaf pair. A minimal fort avoiding u and containing both leaves is exactly their pair. If it contains neither, it is a fort of H and contains some minimal fort A of H; b=0 makes A a fort of G, so minimality forces equality. If it contains just one leaf, its nonempty intersection with H is a fort of H and contains a minimal A; again b=0 makes A a proper subfort of G, a contradiction. The case H empty is included. This proves (3), not merely a listed-subfamily count. Intersections among minimal forts are then inherited exactly from H.

For p>=3, (1) implies Delta(G)>=Delta(H)+3 binom(p,2)-(p+1), whose added term is positive. For p=2,b>0, (2) also has a positive added term. Thus if a tight graph with intersecting minimal forts has a multi-leaf support vertex, either its smaller induced remainder H has negative Delta, or p=2,b=0 and H is a smaller tight graph with intersecting minimal forts. Iterating must terminate. A minimal negative-Delta graph is connected and has no vertex with two pendant neighbors, since (1) would otherwise yield a smaller negative-Delta induced graph (a negative disconnected graph has a negative component).

These facts prove a sharper exact residual formulation: the full target follows from, and implies, BOTH nonnegative Delta for connected graphs with at most one pendant neighbor per vertex, AND equality rigidity for tight connected graphs in that same class. For sufficiency, remove multi-leaf supports to rule out a minimal negative graph; then apply the preceding tight reduction, taking tight components as necessary, to rule out a minimal counterexample. Necessity uses triangle padding to obtain the universal bound and restricts the equality theorem to the class. This leaves genuinely cyclic cores, including graphs without pendant vertices; it does not justify a tree argument there.

As a consistency control, for any base graph J, attach exactly two private pendant leaves to every vertex. In every minimal fort no base vertex can occur, by the pair argument above. Each base vertex must then see zero or two selected private leaves, so the ONLY minimal forts are its private pairs. Thus n=3|V(J)|, m=Z=|V(J)| even with cycles. This supplies known-style tight examples, not a counterexample or a global classification.

## Prior, novelty, significance and Pi gates

Source gate: literal full scope restored, but no live-source explanation for deletion of the conjecture found. Source versions and the relevant block-graph proof were checked. Prior gate: bounded and incomplete. Current LeanPool public HTML reports head 775693e4ac1ff35aa6902480a40f0ce512b28809; its README was retrieved at that immutable head. The current root import file is routing only. r328 had observed 906301dff114598197af816aefe25211ff23a6b0 and a separate Vilin97 head 01db1d7049cf9668bda1e9e106875ee1278b43e6. Neither a landing-page keyword check nor an import file clears the registry's projects or dependencies. No candidate proof body was identified or inspected. No inaccessible prior route was retried. The inherited exact-ID historical match inventory has no 372043 entry; that is not novelty evidence.

Ordinary-math gate: FAILED for the full target; the residual cyclic-core inequalities and equality rigidity above are unproved. Subsumption gate: the transversal reduction, tree equality, component additivity and much of the leaf lifting are already source results or elementary consequences; no credit for these. Novelty gate: NOT CLEARED, and no new full result is claimed. Significance gate: a full faithful resolution could be substantive, but the present reductions and controls are helpers, not an eligible MathDB solution. Credit remains 0; campaign stays 52/60 beyond39.

Pi recommendation: dormant/none. No actual finite witness or concrete qualified finite diagnostic was obtained, so generic enumeration is not proposed. A later proof must cover either the residual core theorem with the reductions above, or a fully specified graph with completeness of ALL minimal forts and a legal forcing argument. Root alone can authorize subsequent Pi implementation using actual graph/fort/process semantics; no proxy hypergraph statistic or partial theorem qualifies.

## Operational evidence

The exact requested bootstrap was the first actual shell command and installed caps before reading AGENTS/TASK. TASK.txt appeared in full in its output. Its first receipt is preserved. All subsequent jobs ran isolated Python -I -B after restricting affinity to the first two allowed CPUs and setting CPU120/AS6GiB before source reads; outer timeouts were 20, 45 or 60 seconds, below wall140. Tool responses report exit 0 for every job; no background jobs, children, or persistent processes were launched. Resource accounting distinguishes self RSS from unavailable process-group/cgroup/managed-service telemetry. Early read-job CPU/RSS were not sampled: command/exit logs attest their caps, not measured peaks. Two oversized metadata outputs were truncated; only the targeted reread excerpts are treated as reviewed. No protected r329 or crown-vnumber path was opened, hashed, globbed, or polled. Other-target frozen inputs were integrity-only and never mathematically reopened.

frozen-before.json verified all 142 expected hashes before mathematical reads. frozen-after.json repeats that verification after all mathematical/source work. Lane-only artifacts are listed with hashes in artifact-manifest.json; no shared, source, author, dependency, ledger, or publication edits were made.
