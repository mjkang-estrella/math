# Research result: zero nominees

Actual work date: 2026-10-30 UTC (the workspace's local date is October 29).
No source conjecture is resolved here. No new credit, Lean development, or manuscript is proposed.

## Three screens

1. **Refined Nordhaus–Gaddum-Type Bounds for Roman and Total Domination on δ-Complement Graphs**, Mathematics 14(11),1797 (2026), DOI 10.3390/math14111797, indexed Conjecture 4: if both G and its δ-complement have no isolated vertices, then γt(G)+γt(Gδ)≤n+2k, with k the number of degree classes. The primary page returned HTTP429 through public web retrieval. No repeat against that host. Search-index text gives the claim and a restricted same-paper theorem requiring each degree-class graph and its complement to be isolate-free. This is **source-access HOLD**, not an exclusion, not a proof, and not eligibility clearance. No mathematical investment on a snippet-defined claim. Author aliases were not established from a readable primary body; this screen is incomplete.

2. **Bastien–Khormali, On link-irregular digraphs**, JCMCC130(2026),227–240, actual published Conjecture3.7, Observation3.6, Observation3.8. The all-order nontrivial tournament target is **publicly proved**, hence excluded. Lily Zhang, arXiv:2610.24631v1, publicly submitted October17,2026, Theorem6 proves all n≥9; the source already constructs orders6,7,8 and excludes orders2–5. This predates this lane. We read the actual pair-constraint/Burnside proof (Lemma2, Theorem3, Lemmas4–5, Theorem6), rather than relying on its abstract. Lemma2 counts components of the induced action of a deletion-card bijection on unordered pairs. Summing over its cyclic vertices gives the exact weight (n−2)! Σ(k=0..n−2)gk. The union bound is < C(n,2)2^(4−n) for n≥10; at n9 the exact bound is3552255/4194304<1. The cited graph-count bound is an external mathematical input, not independently reproved here. The linked author's README explicitly discloses two external Lean axioms; we do not claim its formal certificate meets campaign standards. Its ordinary published proof suffices for the prior-proof exclusion. A separate current Omega dossier and theorem body give a complete alternating-pivot/W construction for every n≥7, plus order6 and small nonexistence. Read current actual bodies, not just its theorem label. This is additional overlap, not a new result of this lane; public Lean was not compiled or fully dependency-audited here. Source's nontrivial convention matters: n0,1 are vacuous; no discovery is claimed from that correction.

3. **Dovzhenok–Lukashenko–Mikhalev–Filiuta, On infinite families of [Pn]-irregular graphs**, arXiv:2609.24707v1, September21,2026, Definition1 and **Conjecture3**. This is the pursued target. For every connected finite simple F with |V(F)|≥3, infinitely many finite simple graphs G should have pairwise distinct numbers

    cF(G,v)=#{S⊆V(G): |S|=|F|, v∈S, G[S]≅F}.

The current abstract/version page exposes v1 only and no journal reference; this is a bounded source observation, not a guarantee no published version exists. The source itself proves all paths in Theorem1 and exact P3 orders in Theorem2. These cases cannot be repackaged as discoveries. Conjectures1–2 in its introduction count ordinary subgraphs; Conjecture3 explicitly changes to **induced** subgraphs. The nearby Dovzhenok–Filuta arXiv:2609.19245v1 has a full ordinary-F construction, not an induced-F theorem. Its introductory definition was read from the PDF; formula OCR is damaged, so no audit of its complete proof is claimed. No logical exclusion of Conjecture3 is inferred from it.

## Sustained mathematical investigation of Conjecture3

### The exact cancellation that prevents an ordinary-count transfer

Label F by [m]. Write Axy∈{0,1} for adjacency in G. The induced count at v is exactly

    1/|Aut(F)| Σφ:[m]↪V(G), v∈im φ
      ∏ij∈E(F) Aφ(i)φ(j) ∏ij∉E(F),i<j (1−Aφ(i)φ(j)).

Every induced vertex set is counted |Aut(F)| times, proving the formula. Expanding the second product is inclusion–exclusion over missing edges. For each S⊆(C([m],2)\E(F)), it contributes (−1)^|S| times the injective labeled count of F+S, divided by |Aut(F)|. Thus ordinary-F irregularity alone controls only the S=∅ summand. It provides neither sign nor collision control on the alternating correction. Distinct ordinary counts can become equal induced counts.

For F=P3 the identity becomes particularly transparent. If dv is the degree and tv the number of triangles through v, then

    cP3(G,v) = C(dv,2) + Σu∈N(v)(du−1) − 3tv.

The first term counts paths centered at v; the second counts paths with endpoint v. Every triangle contributes three non-induced paths containing v, so subtract three. In K3 every vertex's ordinary path count is3 but its induced count is0. This is a correction identity and method warning, not a counterexample to the source. The capped checker verifies this identity at all5400 vertices of all1096 labeled graphs of orders3–5.

### Generic distinct expectations really can be obtained—and are insufficient

Take independent edges with probabilities pe in (0,1). For fixed v, E cF(G,v) is a multilinear polynomial in all pe. For any u≠v and N≥m+1, the difference polynomial is nonzero: specialize the graph to one induced F on a set containing u and excluding v, and make all remaining vertices isolated. Connectedness and m≥3 give cF(u)=1 and cF(v)=0. Consequently the finite product of all pair-difference polynomials is nonzero. A nonzero real polynomial cannot vanish on the open cube (prove by induction on its variables using the univariate finite-root fact). Hence some interior probability vector makes **all expected counts pairwise distinct**.

This establishes only a generic expected-count statement. It does not yield even one irregular realization. The exact control uses N4,F=P3, pij=(i+1)(j+1)/100 for zero-based labels i,j. Expected counts are

    4517/250000, 7193/250000, 8133/250000, 2153/62500.

They are distinct. Every graph has positive product probability, but exhaustive enumeration of all64 labeled four-vertex graphs finds **no** irregular realization. Indeed the source's exact threshold is7; the independent finite control needs no reliance on that theorem. Therefore an argument selecting a realization from unequal expectations is false even inside the source's allowed F class. This failure is stronger than merely lacking a concentration estimate.

Making every edge probability tiny cannot repair it. If e=|E(F)|, a union bound over injective labeled copies gives P(G contains any ordinary F)≤(N)m ε^e when all pe≤ε (where (N)m is the falling factorial). This tends to0 as ε→0 for fixed N. If G has no F then all its induced counts vanish. A leading small-probability expansion that separates expectations therefore allows irregularity probability to tend to0. No quantitative all-N anti-concentration estimate was obtained.

### Clone/blow-up and disconnected amplification obstructions

If a construction replaces one vertex by two or more independent twins (or a clique of true twins), any transposition within that part is an automorphism. It bijects induced F copies containing either vertex. Thus the entire part has equal counts for **every** F, independently of part sizes. Unequal blow-up sizes do not distinguish vertices inside a part. A P3 blow-up with part sizes1,2,3 has counts[7,10,10,7,7,7], directly checked. It is a route falsifier, not a source counterexample.

For connected F, an induced F cannot cross components. Thus disjoint union preserves each component's count list without multiplying it. Repeating an irregular component repeats every count. Adding two isolated vertices repeats0. One cannot derive infinitely many irregular graphs merely by duplicating a finite witness or adjoining arbitrary isolates.

## Precise remaining step and strongest objections

We have no construction or probability bound producing a single [F]-irregular graph for an arbitrary connected F, much less an unbounded sequence of graph orders. An adequate probabilistic route must bound **integer collisions**, e.g. establish Σu<v P(cF(u)=cF(v))<1 for some unbounded sequence of N with suitable nonuniform edge probabilities. No such bound follows from the generic expectation polynomial argument. A deterministic route needs gadgets that distinguish all their own vertices while controlling all induced copies crossing attachment interfaces; no such gadget invariant is proved.

The full source claim is not refuted by small nonexistence, by clone collisions, by missing anti-concentration, or by failure of disjoint-union amplification. Those are method obstructions only. Complementing G transports counts to the complementary pattern exactly, but the complement of a connected F may be disconnected; it does not reduce every connected pattern to the path/ordinary theorem. No routine/classical exclusion is asserted without a complete bridge. Source path cases and ordinary-F construction are uncredited.

## Historical and public scope limits

Full original SUMMARY/discovery/PROOF/review/DECISION bodies were queried before source downloads using exact IDs, titles and author/claim aliases; the qualified r156 baseline was refreshed for changed/new originals. Query output is retained in history-receipt.json, with original r111–r113 science paths explicit. Initial overbroad alias1797 caused spurious hash matches; its copied bodies are retained as a failed search artifact, not treated as relevant prior science. The final precise aliases have no matches in that scoped body set. This does not prove worldwide novelty.

CURRENT Omega and OpenAI heads and fixed evidence are in registry-screen.json. Targeted current actual tournament bodies were read. Two inherited300-file-capped comparisons remain incomplete. Lexical no-hits for the induced target give no semantic absence clearance. No full new-head inventory or exhaustive body audit is claimed. Public web search returned no additional induced-target proof in the bounded exact-title/ID/conjecture queries. That is not a proof of openness. The delta-complement429, companion HTML404, OCR limitations, and formal-input limitations remain live qualifications.

The Malik–Qureshi known exception, Su read-once target, weighted Bernoulli target, and Kazemi exclusion are untouched. No credited-family variant is nominated.
