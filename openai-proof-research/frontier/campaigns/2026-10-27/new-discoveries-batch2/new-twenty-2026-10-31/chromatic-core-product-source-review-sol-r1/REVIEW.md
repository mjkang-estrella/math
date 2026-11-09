# Independent review: 338603 / 338604, one family

Reviewer: GPT-6.1 Sol, high/default, personally; no children, fallback, mathematical programs, or formal execution. Reservation SHA256 4f2c014317a2128d8c90c512acdb3ba871653514f5a4e42a9976d3b5c50dcc10. Root count remains 55/60 beyond 39, 94 total; credit zero.

## Decision

338603: ordinary mathematics PASS; primary-source fidelity PASS; literal strong-product binding PASS. The 10-vertex witness refutes the universal statement. Prior-to-target bridge COMPLETE from an authenticated 1993 primary theorem, with every additional step supplied below. Recommend exclusion from substantive discovery credit as a routine adaptation of that earlier product-coloring result and its accompanying independence bound. This is a significance/prior-subsumption judgment, NOT an assertion that a published explicit chromatic-core refutation was located. Exact-public-refutation novelty remains unresolved within the bounded search. No acceptance decision is made here.

338604: source lexicographic Conjecture 3 refuted by the same witness, ordinary mathematics and source gates PASS. Its literal unnamed circledast remains HOLD: the record expressly says the operation lacks a standard definition. Context strongly favors lexicographic product but does not authorize silently replacing this literal ambiguity. Same family and same prior/significance assessment; never a second credit.

Formal gate NOT RUN for both. No kernel theorem, dependency audit, library availability measurement or extracted replay is claimed. Prospective qualification is not established; no dormant next-execution brief is issued.

## Source fidelity and conventions

Complete copied JSONL records were read. Complete extracted text of Kok, Naduvath, Seles and Mary, *On Chromatic Core Subgraph of Simple Graphs*, Contemporary Studies in Discrete Mathematics 2(1) (2018), 13–20, was read in overlapping parts. Re-extraction of the supplied PDF exactly matches the supplied text. Header independently confirms publication online 23 February 2018, and arXiv v1 stamp 5 March 2018. The fresh primary landing page on 8 November 2026 UTC lists only v1, submitted 5 March 2018 05:48 UTC; it does not establish absence of an independent journal corrigendum.

Definition 1, printed p14, minimizes si(H)=|V(H)|+|E(H)| over INDUCED subgraphs with chi(H)=chi(G). This is a finite global minimum, not a homomorphism core or merely an inclusion-minimal subgraph. The whole graph is allowed: the definition does not require properness and Proposition 1(iii),(iv) explicitly give whole odd cycles and complete graphs as their own unique cores. Our proof of those two instances is independent of that proposition. All our graphs are finite, nonempty, connected, undirected and simple. The introduction allows disconnected graphs, with p14 explaining reduction to a component of maximum chromatic number and least core size; our witnesses need no disconnected convention. Allowing an empty induced subgraph with chi=0 does not affect any positive-chromatic minimum here. No uniqueness of minimizers is assumed in general; uniqueness is proved for the two chosen factors.

Section 3.5 p18 defines standard strong adjacency, and Conjecture 2 matches 338603 exactly. Section 3.6 p18 explicitly defines lexicographic adjacency, and Conjecture 3 is the associated source claim for 338604. The adjacent discussion of a 'general graph product' does not supply a unique definition of the record's circledast. Its argument from edge counts and induction on a conjecture is not a proof. The source's Lemma 1 critical-graph classification and other broad assertions are not imported. In particular Brooks' theorem cannot classify all vertex-critical graphs as cliques or odd cycles. No upstream OpenAI theorem is used.

## Independent complete proof

Write C5 on Z/5Z with adjacency difference +1 or -1, and K2 on {0,1} with distinct vertices adjacent. A two-coloring of C5 would alternate around its odd cycle and return the wrong color to the starting edge. The colors 0,1,0,1,2 around the cycle give chi(C5)=3. Deleting any vertex leaves a path on four vertices; every proper induced subgraph is an induced subgraph of such a path. Alternating along the path gives a two-coloring, whose restriction works on every subset, including disconnected subsets. Thus the only induced subgraph of C5 with chi=3 is C5 itself: its core is unique and globally minimum. Similarly chi(K2)=2 and every proper induced subgraph has chromatic number at most one, so its unique core is K2.

The independence number of C5 is two. The vertices 0 and 2 are independent. Three independent vertices would need a gap of at least two cycle steps between each cyclically consecutive pair; three such gaps require at least six steps in a cycle of length five. This proves the upper bound without a subset sweep.

For vertices (i,a),(j,b), strong adjacency is
(i~j and a=b) or (i=j and a~b) or (i~j and a~b).
Since K2 is complete, when i~j the two alternatives a=b and a~b exhaust all second-coordinate pairs. Thus the adjacency is exactly
 i~j OR (i=j and a!=b),
which is lexicographic adjacency for C5[K2]. This also distinguishes the Cartesian product: between adjacent fibers it only joins matching second coordinates, omitting the strong product's diagonal edges. The tensor product alone omits matching-coordinate edges and within-fiber edges. No ambiguity about these operations enters 338603.

Let X=C5 strong K2=C5[K2]. A fiber is a clique K2, so an independent set meets it at most once. Distinct occupied fibers must have nonadjacent first coordinates. Projection is injective on the independent set and gives an independent set of C5. Hence every independent set of X has at most two vertices; size two is attained at (0,0),(2,0).

Give (i,0) color i and (i,1) color i+2, all modulo five. Within a fiber these colors differ by two. For a cyclic step i to i+1, the color sets {i,i+2} and {i+1,i+3} are disjoint: any putative equality would require a difference among 1,-1,3 to be zero modulo five. This treats every edge, including the wrap from fiber 4 with colors {4,1} to fiber 0 with colors {0,2}. It is a proper five-coloring.

Let Y be the induced subgraph on all vertices except (0,0). It has nine vertices. Its independent sets are independent in X, so have size at most two. Every color class is independent. Four classes therefore contain at most eight vertices, too few for Y. Thus chi(Y)>=5. Restricting the displayed coloring gives chi(Y)<=5; extending the lower bound by induced-subgraph monotonicity gives chi(X)>=chi(Y)=5, and the full coloring gives chi(X)<=5. Therefore both chromatic numbers are five.

X has ten vertices. Each has one neighbor in its own fiber and two in each neighboring fiber, all distinct, so degree five. The handshake identity yields 25 edges. Removing (0,0) removes exactly its five incident edges and no others: Y has nine vertices and twenty edges. Thus si(X)=35 and si(Y)=29. More generally vertex deletion strictly decreases si by 1+degree, so exact edge counting is not essential.

For G=G'=C5 and H=H'=K2 the proposed product of factor cores is X itself. But Y is an induced same-chromatic subgraph with strictly smaller si. Consequently X cannot be a GLOBAL minimum in Definition 1. This single competitor disproves corehood: neither a classification nor the numerical value of the actual minimum core is required. It refutes 338603 and the source lexicographic Conjecture 3 simultaneously. It does not by itself repair 338604's literal binding.

The optional 25-vertex proof was read as part of FULLCANDIDATE, but is not needed, not an independently credited endpoint and not used to strengthen qualification. This review's certified ordinary proof is the 10-vertex argument above.

## Actual earlier primary theorem and complete bridge

Newly acquired: Sandi Klavzar, *Strong products of chi-critical graphs*, Aequationes Mathematicae 45 (1993), 153–162. The author-hosted CHI.pdf is a complete readable primary manuscript (13 manuscript pages), read in full. The separate published scan authenticates the journal, year, pages and statement/proof: images of printed pp153,155–157 were personally read. On printed p155, Lemma 3 gives chi(F)>=|V(F)|/alpha(F) and alpha(G strong K_n)=alpha(G). Theorem 4 at pp155–156 states, for chi-critical G and arbitrary H,
 chi(G[H]) <= chi(H)(chi(G)-1)+ceil(chi(H)/alpha(G)).
The complete proof on p156 was read, including its quotient/remainder construction, separation of colors divisible by chi(G), and the two equality-of-color cases. This is an actual applicable theorem/proof body, not a search abstract. The published scan p153 states manuscript received July 3, 1991, final form July 8, 1992; publication is 1993, well before February 2018. The manuscript's Theorem 2 attributes a lower bound to Stahl 1976 and section 4 attributes the odd-cycle multicoloring formula to him, but Stahl's original body was not obtained and is not independently relied on.

Here is the entire bridge, including the steps absent from the earlier paper's terminology:

1. The factor proof above makes C5 chi-critical with chi=3 and alpha=2, and K2 has chi=2. Theorem 4 therefore supplies a five-color upper bound for C5[K2]: 2(3-1)+ceil(2/2)=5. Its exact hypotheses are met; no false classification of critical graphs is used.
2. Strong and lexicographic adjacency coincide with complete second factor, as checked above. Lemma 3(ii), or the direct projection proof, gives alpha(X)=2.
3. For the induced deletion Y, every independent set is still an independent set in X, hence alpha(Y)<=2. Nine vertices cannot be partitioned into four independent sets of size at most two. This is the deletion-stability bridge, not a conclusion from chi(X)=5 alone. Inherited upper coloring yields chi(Y)=5, hence chi(X)=5 as well.
4. The independently proved factor uniqueness supplies G'=G,H'=H under the source's permitted whole-factor convention. The deletion reduces si strictly, since one vertex and its incident edges disappear.
5. Definition 1 then excludes X from global minimizers by the explicit competitor Y. This addresses the FULL global si condition; no edge-minimal/vertex-critical/homomorphism-core substitution occurs. These deductions apply to Conjectures 2 and 3 as one family.

The earlier theorem supplies more than a familiar chromatic number: its paper places the upper bound alongside exactly the independence framework that supplies the lower and deletion bounds. The additional target bridge uses independent-set monotonicity under induced deletion, a cardinality inequality, and the definition of a global minimum. No new product theorem, new minimizer classification or special structural lemma remains. Under this campaign's express exclusion of routine corollaries/adaptations, this is a concrete reason for the significance FAIL recommendation. It is not based on small graph size, ease, proof length, tools or a snippet.

## Strongest objections and contrary case

The strongest case for significance is that the earlier result never mentions chromatic cores or claims this refutation, and deletion-stability is logically additional. A known value chi(X)=5 alone would NOT prove the target false: critical five-chromatic graphs lose chromatic number on deletion. The author correctly supplies this missing argument. Also, a direct refutation of a published universal conjecture is mathematically useful, even if short; the source's incorrect general claims do not remove the need for a literal counterexample.

Nevertheless, here the earlier source explicitly gives both the relevant upper theorem and alpha bound. Applying its counting bound after deleting one of ten vertices still forces five colors. The global-minimum step then follows directly from the definition, and factor uniqueness follows from elementary cycle deletion. This is a complete documented routine bridge, not merely the assertion that product coloring is known. The best contrary case supports preserving the correction as an ordinary project finding; it does not establish the requested substantive novelty beyond an earlier theorem adaptation. Root must adjudicate that recommendation. A later explicit primary refutation, if identified, would strengthen exclusion, but is not asserted to exist.

Specific prior leads not promoted to evidence: Geller–Stahl 1975, Stahl 1976, Cizek–Klavzar 1994, and Godsil–Royle's book discussion. Searches surfaced identities/formulas and bibliographic pointers; their original applicable bodies were not reviewed in this lane. They are unnecessary for the complete 1993 bridge, and receive no proof or novelty-clearance weight. No exact earlier public chromatic-core counterexample body was located. Generic worldwide uncertainty is not treated as a mathematical veto.

## Coverage and process limits

Two native searches, six exact query strings, live counters charged before calls, full responses retained. Seven guarded GET hops, all successful HTTP200 without redirects; each shared source and registry root charged to BOTH IDs. No other GET client or native fetch/open used. One hop left unused. Fresh arXiv version metadata and fresh four registry roots checked. Registry heads match inherited displayed values; roots are metadata only, no matching proof bodies or exhaustive public-corpus review. The correction search surfaced the original paper and copies, not an inspected corrigendum. Current independent journal/author citation coverage remains bounded and incomplete.

All local substantive operations ran under unchanged run.py; writes used write_lane.py except immutable guard payload/ledger/lock and the explicitly exempt initial/final verifiers/bootstrap. The first receipt is preserved. OCR attempt failed because tesseract was absent (exit 1); no install or unchanged retry. The scan was instead rendered and personally read; empty pdftotext output was never treated as a body. Source processing/rendering is not mathematical execution. The source is a scanned primary body, not an unavailable network artifact.

Runner receipts record affinity [0,1], child CPU115/supervisor120 seconds, AS6GiB, 130-second supervisor deadline, arena2, sampled group RSS guard6GiB, synchronous reaping and true exits. Native search CPU/RSS unavailable. Short jobs can have sampled peak zero; sampling misses transients. Writer has its own caps, without separate writer/group high-water measurement. No universal resource-compliance claim follows. Final inventories and manifest specify their terminal self-exclusions.

All content reads were confined to the assigned lane/copied inputs except printed ancestor instructions and the initial/final verifier's authorized hash-only bindings, including 124 author references. Protected active peers, old formal bodies, shared ledgers and original author contents were not opened. No shared writes, git, publication, messages, children, background jobs or formal dispatch. Final frozen-after result is in frozen-after.json and incorporated in the terminal manifest. No acceptance or credit is awarded.
