Interpolation of orientable total domination by safe arc reversals

DRAFT research manuscript · MathDB 360905 · 4 November 2026 (Pacific time)

Prepared with OpenAI Codex AI assistance for mathematical exposition, source comparison, computation and document production. No human authorship or affiliation is asserted. This is an unpublished draft; acceptance and campaign credit remain solely with root.

1. The problem and its domain

An orientation D of a finite simple undirected graph G directs each edge in exactly one of its two directions. Write u → v for an arc of D. The orientation is valid if every vertex has positive indegree. A set S ⊆ V(G) totally dominates D if every vertex v, including every vertex of S, has an in-neighbour in S: there is u ∈ S with u → v. Let γt(D) be the minimum size of such a set. For valid D the whole vertex set is a total dominating set, so this minimum exists.

For a graph admitting a valid orientation, define its spectrum Σ(G) = {γt(D) : D is a valid orientation of G}, and define domt(G) = min Σ(G) and DOMt(G) = max Σ(G). There are finitely many orientations, so both extrema are attained. The admissible nonempty graphs are precisely those whose every component contains a cycle. Indeed a tree component has fewer edges than vertices and cannot have positive indegree everywhere. Conversely, orient a cycle cyclically in each component, attach the remaining vertices along a spanning tree rooted on that cycle, and direct the tree edges away from the cycle; direct all remaining edges arbitrarily. Each vertex retains an incoming arc. The empty graph is also admissible under the vacuous convention, with spectrum {0}.

Hansen, Lai and Yue [1] used the name open domination, with notation ρ1, dom1 and DOM1 for the same parameters. Their final, unnumbered Conjecture on printed page 181 reads verbatim (mathematical typography transcribed):

“Let G be a graph. If c is an integer for which dom1(G) ≤ c ≤ DOM1(G), then there exists an orientation D of G such that ρ1(D) = c.”

Anderson, Dravec, Johnston and Kuenzel [2], arXiv v1, state:

“Conjecture 3.1. [10] Let G ∈ C and let c be any integer such that domt(G) ≤ c ≤ DOMt(G). Then there exists an orientation f of G such that γt(Gf) = c.”

Here C is their class of connected graphs containing a cycle. Their reference [10] is Holley–Lai–Yue [3], whereas their reference [8] is Hansen–Lai–Yue [1]. Thus the immediate attribution in v1 differs from the brief's shorthand, although [1] directly prints the general conjecture. The raw MathDB record's first-stated year is the preprint year; it does not capture the older printed statement.

Theorem. For every finite simple graph G admitting a valid orientation, Σ(G) is an integer interval. Equivalently, each integer between domt(G) and DOMt(G) is γt(F) for some valid orientation F of G.

Theorem 14 of [1], printed page 180, establishes the complete-graph case by vertex deletion and extension. Theorem 3.6 of [2] establishes the complete-bipartite case. The proof below uses neither construction and applies directly to disconnected graphs.

2. A transfer lemma and the complete proof

Fix valid orientations D and E of the same finite simple graph. Define Δ(D,E) = {(a,b) : a → b in D and b → a in E}, and put d(D,E) = |Δ(D,E)|. Each disagreeing edge contributes exactly once. A target-directed flip reverses an arc in Δ(D,E), thereby making that edge agree with E.

Lemma 1 (forced heads). Suppose that every arc a → b in Δ(D,E) is the unique incoming arc at b in D. Then every total dominating set of D is a total dominating set of E.

Proof. Let S totally dominate D. First we show that every head of an arc in Δ(D,E) belongs to S. Let a → v be such an arc. Choose w → v in E, using validity. If w → v also occurred in D, uniqueness at v would force w = a, contradicting reversal of a → v. Since the underlying edges are the same, v → w occurs in D and is reversed in E. By the hypothesis it is the unique incoming arc at w in D. Since S dominates w in D, its only possible witness is v, so v ∈ S.

Now let v be any vertex, and choose a ∈ S with a → v in D. If this arc survives in E, it dominates v there. Otherwise a → v lies in Δ(D,E). Choose w → v in E. As above, w → v cannot occur in D, and hence v → w lies in Δ(D,E). The first part of the proof, applied to its head w, gives w ∈ S. Thus w → v witnesses domination of v in E. This holds for every v, proving the lemma. □

Lemma 2 (safe flip and repair). If S totally dominates D but does not totally dominate E, there are a → b in Δ(D,E) and another incoming arc w → b in D with w ≠ a. Reversing a → b gives a valid orientation F of the same graph such that S ∪ {w} totally dominates F and d(F,E) = d(D,E) − 1.

Proof. If no such arcs existed, every disagreeing arc would be the unique incoming arc at its head. Lemma 1 would imply that S dominates E, a contradiction. Choose the stated a,b,w and perform the flip. Only b loses an incoming arc, and it retains w → b; all other vertices retain their old incoming arcs. Thus F is valid, and it is still an orientation of G. To check total domination by S ∪ {w}, use w at b and each old S-witness at any other vertex. This includes the new vertex w itself: its old witness is retained, since w ≠ b by looplessness. Finally, the changed edge now agrees with E, and no other edge changes. Exactly one element is removed from the disagreement set. □

Proof of the theorem. We prove the stronger statement that, for any valid D,E and integer c with γt(D) ≤ c ≤ γt(E), a valid orientation of the same graph attains c. Use strong induction on d(D,E). If γt(D) = c, take D. Otherwise let S be a minimum total dominating set of D. Then |S| = γt(D) < c ≤ γt(E), so S cannot dominate E. Lemma 2 supplies a valid F with

γt(F) ≤ |S ∪ {w}| ≤ γt(D) + 1 ≤ c,

and smaller disagreement with E. Apply the inductive assertion to F,E and c. The induction is well founded on nonnegative integers; when disagreement is empty the orientations coincide, so the strict case cannot arise. Taking D and E attaining the two extrema proves the claimed interval. □

There is no connectedness assumption anywhere in this argument. In particular all vertices in all components are quantified in each total-domination assertion, and the induction changes only an existing edge. It handles every admissible disconnected graph as stated. Alternatively, total domination numbers add over components, and sums of finite integer intervals are integer intervals. The empty case has the value already specified.

3. Why validity matters; fresh finite confirmation

For ordinary domination, members of a dominating set need not themselves have incoming witnesses from that set. If an arc a → b is reversed, adjoining b repairs any loss of ordinary domination. Applying the same observation in reverse shows that the ordinary domination number changes by at most one. Every orientation remains admissible, and any two orientations can be joined by reversing their disagreeing edges one at a time. This explains an ordinary-domination interpolation mechanism associated with the problem studied in [4]. It is an independent argument here, not a claim to have read or reconstructed the actual proof in the unavailable 1996 paper.

For total domination the admissible orientations can be disconnected under single-edge flips. On a cycle Cn, n ≥ 3, positive indegree and the edge count force every indegree to equal one. Thus the only valid orientations are the two directed cycles. Reversing any single arc leaves its old head with indegree zero. Moreover each predecessor is forced into every total dominating set, so both orientations have total domination number n. There is no valid first flip between them. Lemma 1 replaces the missing path argument: when all target-directed flips are blocked, domination transfers to the target. Lemma 2 then supplies a flip whenever a strict numerical gap requires progress.

For a concrete check, the directed triangle with arcs 0 → 1, 1 → 2, 2 → 0 and its reverse both have γt = 3; their disagreement is 3, and all three individual reversals are invalid. Fresh enumeration also checks both directed orientations of C4 and C5, with total domination numbers 4 and 5 respectively. These examples illustrate the obstruction rather than an exception to interpolation.

The isolated Python program scripts/recompute.py enumerates every assignment of absent, forward or backward to each unordered vertex pair. At each valid leaf it tests vertex subsets by cardinality, requiring their out-neighbourhood union to equal the whole vertex set, and records the minimum in the spectrum of that underlying labeled graph. Subsets of cardinality below three may be skipped: a nonempty total dominating set induces a finite digraph of positive indegree, hence a directed cycle, and an asymmetric loopless digraph has no cycle shorter than three. Every orientation of every labeled simple graph is visited exactly once. No solver or imported enumeration result is used.

Order

Admissible graphs

Valid orientations

Gaps

3

1

2

0

4

22

122

0

5

603

16,168

0

6

25,418

5,545,708

0

The columns count admissible labeled graphs and valid orientations over all graphs; each row has zero spectra with a missing integer. For order 6, restricting the fresh results to connected graphs gives 25,408 graphs and 5,545,668 orientations. The extra 10 graphs are the labeled disjoint unions of two triangles, with 40 orientations in total. This reconciles discovery's connected counts with review's all-graph counts; it is a scope difference, not a counterexample.

The complete per-graph spectra and counts are retained in recomputed/spectra.json, with aggregate comparisons and explicit cycle checks in recomputed/verification.json. The run is split by the state of the first vertex pair so that each foreground call stays within the resource caps. Historical review independently enumerated all graphs through order 6 and checked pair/set witnesses through order 4. Its attempted order-5 pair run was killed by its cap and is not claimed as completed evidence. Finite confirmation supports implementation fidelity; the general theorem rests on the proof, not on enumeration.

4. Formal correspondence and the evidence boundary

The preserved Lean packet proves the endpoint OrientableTotalDomination.conjecture_true : OrientableTotalDomination.Conjecture in module Interpolation. The table records the mathematical meanings of the actual source definitions, rather than treating the theorem name as evidence of scope.

Rel / Arc

Boolean adjacency / equality to true.

Valid

Every vertex has an incoming arc.

Asym

No opposite arcs, hence no loops.

Same

Identical underlying undirected support.

OrientationOf G D

Asym D and support exactly G.

TD D S

Every vertex has an in-neighbour in S.

Minimum D S

TD D S and |S| ≤ |T| for every TD set T.

spectrum G

Attained minimum sizes, within 0,…,|V|.

lower / upper

Actual min′ and max′ of nonempty spectrum.

Conjecture

All intermediate sizes belong to spectrum.

conjecture_true

A proof of this literal Conjecture.

The source uses arbitrary finite vertex types. OrientationOf implies symmetry and looplessness of any Boolean support that has a witness, so quantifying all Boolean supports introduces no invalid graph instances. Conversely each finite simple graph has such a representation. The finite spectrum is nonempty exactly when a valid orientation exists: minimum_exists supplies a literal cardinal minimum, and every subset has cardinality at most |V|. The spectrum cutoff therefore loses no values. Natural-number quantification suffices for the source's integers because a cardinality lower bound makes every integer in the interval nonnegative.

The proof correspondence in Interpolation.lean is precise. Lines 26–34 prove existence of minima. Lines 36–68 (safe_edge) prove the contrapositive forced-head transfer and extract the repairable edge. Lines 70–131 verify flip semantics, asymmetry, support, validity and domination repair. Lines 133–151 prove strict decrease of disagreement; the ordinary proof establishes the sharper decrease by exactly one. Lines 155–181 (interpolation) implement strong induction between two attained minima. Lines 184–215 define the actual spectrum and extrema and derive the final conjecture. No connectedness or special graph-class hypothesis enters.

The packet manifest pins Lean 4.34.1 and mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612. The supplied independent review reports a fresh extracted strict compile, explicit-module kernel check and module-wide audit. Its audit covers 38 local/generated declarations, checks unsafe and partial declarations and executable substitutions, and allows only the transitive axioms propext, Classical.choice and Quot.sound. The parent replay receipt independently reports PASS for the build, explicit Interpolation kernel check and root metadata inspection, again with 38 module-owned declarations and the same allowed axiom closure. These are reports of preserved earlier runs, not new formal executions for this manuscript.

For this dossier, the original packet was copied byte-identically and its SHA-256 checked against the brief. A fresh extraction rejected absolute paths, traversal, symlinks and oversized content, then compared all extracted member hashes. There are four source/metadata members and no execution was performed. This lane ran no Lean, lake, leanchecker or solver. The packet's original manifest still says independent review and root acceptance are pending: it is historical metadata retained unchanged, while the later review and root ruling document subsequent decisions.

Trust limits remain explicit. The reported replays reuse pinned dependency oleans; they do not constitute a full rebuild of upstream mathlib or a validation of the compiler implementation. The safe-extraction test checks archive integrity, not proof validity. The parent's registry refresh is CLEAN for its stated catalogue and complete-tree path screens, not a full-body or worldwide proof search. All those receipts and the earlier failures remain in the source snapshot.

5. Related work, qualifications and reproducibility

The historical complete-graph vertex-deletion proof [1] and the complete-bipartite orientation construction [2] settle genuine special cases. Blázsik and Nagy [5] characterize the upper-extremal condition DOMt(G) = |V(G)| − 1; the inspected text does not supply general interpolation. This draft's contribution is the full finite-graph assertion via the blocked-flip transfer lemma. Its proof is short and elementary. The root ruling calls its significance “QUALIFIED_PASS, modest-to-substantive”; no priority claim or worldwide novelty certification is made.

The controlling ruling is orientdom-root-ruling-r2.json. Its gate_D_ruling qualifications are reproduced below exactly, including the rationale for proceeding despite unread sources. These are root's adjudications; the earlier independent review and follow-up remain HOLD reports and are preserved without alteration.

The 1996 Chartrand-VanderJagt-Yue paper (Congr. Numer. 119) exists only in print and could not be read by legitimate open routes; this is a qualified limitation under the closed-access precedent (388087/324342) because positive evidence shows its method does not settle the total-domination case:

(i) B. Q. Yue co-authored the 1996 interpolation paper and then posed the total-domination interpolation statement as an open conjecture (proving only the complete-graph case by vertex deletion);

(ii) Anderson-Dravec-Johnston-Kuenzel (arXiv:2311.16307v1, lines 321-327 and reference [5]) cite the 1996 paper and still state Conjecture 3.1 as open, proving only complete bipartite graphs;

(iii) Blazsik-Nagy (arXiv:2411.04560 and 2026 published text) treat it as open;

(iv) mathematically, single-arc continuity suffices for ordinary domination because every orientation is admissible, while validity can block flips for total domination; the candidate's forced-head lemma is exactly the repair and appears in none of the inspected sources.

The published DAM 382 (2026) version is closed access (ScienceDirect denied): unread version of record is a qualified limitation with positive retention evidence (publication record; arXiv v1 is the only version; indexed publisher excerpts; later citing text treats the conjecture as open). Citing-work coverage is bounded (OpenAlex rate-limited; cited_by_count 0).

The dossier contains the paper source and PDF, a standalone proof, exact MathDB raw bytes and hash, frozen source copies with original acquisition receipts, the unchanged Lean packet, extraction receipt, fresh scripts and spectra, page renders and QA receipt. Hash manifests bind frozen inputs before and after this work. The computational values in this paper are regenerated by isolated Python scripts; bibliographic dates, theorem labels, version numbers and formal-run counts are documentary metadata checked against the preserved inputs, not mathematical computations. No network retrieval or formal replay was performed in this lane. The campaign context supplied with the task is 42/60 beyond 39; this draft awards zero accepted credit, and only root can accept.

References

[1] Lisa Hansen, Yung-Ling Lai and Bill Quan Yue. Orientable Open Domination of Graphs. J. Combin. Math. Combin. Comput. 29 (1999), 159–181. Original scan inspected: title page and printed pages 179–181; conjecture on page 181 is unnumbered. No DOI asserted.

[2] Sarah E. Anderson, Tanja Dravec, Daniel Johnston and Kirsti Kuenzel. Orientable total domination in graphs. arXiv:2311.16307v1 (2023), Conjecture 3.1 and Theorem 3.6. Discrete Appl. Math. 382 (2026), 48–59. DOI: 10.1016/j.dam.2025.11.031 (verified publication metadata in inputs; journal body unread).

[3] L. Holley, Y. L. Lai and B. Q. Yue. Orientable step domination in graphs. Congressus Numerantium (1996), 129–144. Bibliographic entry as printed in [2], reference [10]; primary body not inspected here and volume not supplied there.

[4] G. Chartrand, D. W. VanderJagt and B. Q. Yue. Orientable domination in graphs. Congr. Numer. 119 (1996), 51–63. Bibliographic data from [2], reference [5]; print-only body unread.

[5] Zoltán L. Blázsik and Leila Vivien Nagy. Characterization of graphs with orientable total domination number equal to |V| − 1. arXiv:2411.04560 (2024); Discrete Appl. Math. 378 (2026), 234–243. DOI: 10.1016/j.dam.2025.07.021 (printed in preserved journal text).
