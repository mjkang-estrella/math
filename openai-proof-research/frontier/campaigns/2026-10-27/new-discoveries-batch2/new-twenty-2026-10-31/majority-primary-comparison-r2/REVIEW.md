# MathDB 326640 — independent primary-proof comparison r2

**Overall HOLD. The Caro–Henning author manuscripts have now been obtained and their relevant proofs inspected; no subsumer was found there. The material 1996 primary-proof gap remains.** Source fidelity, mathematical correctness and the existing strict Lean PASS are preserved. Intrinsic significance remains PASS conditional on qualified novelty. Recommended actual credit: **0**; conditional family credit: **1**, subject to the remaining comparison and root adjudication. The campaign remains 1/20 accepted; this review changes no count.

## Binding, scope and exact endpoint

Work is confined to this folder. `integrity-before.json` binds every file in the frozen author packet and both earlier review folders before this investigation; `integrity-after.json` checks the same paths and inventories additions/deletions. See `integrity-result.json` for the comparison. Earlier evidence is referenced in place, never overwritten. Applicable ancestor AGENTS.md files, ancestor ledger/context, source catalogue/pin, prior significance report, source inventory and all its retrieval receipts, author retrieval receipts, PROOF.md and the fidelity review decision were read. No git, subagents, browser tabs, author messages, publication or Lean reruns were used.

The target is exactly arXiv:1311.0479v1, Definition 4.1 and Conjecture 4.10: positive integers r≤s, with upper orientable **set majority** domination DOM≠1, have DOM=2 if s≤r+2 and DOM=ceil((s−r)/2) otherwise. Minimum selected-set cardinality is taken inside a maximum over every orientation. A selected set covers the **union of closed out-neighborhoods**, with threshold h=ceil((r+s)/2). Full domination, signed functions, multiple domination and distance-two domination are different predicates.

The frozen proof's decisive step is the opposite-part pair. For maximum outdegrees a on the r-part and b on the s-part,

    rs ≤ ra+sb ≤ s(a+b).

Thus a+b≥r; when r<s and some smaller-to-larger arc exists, a>0 makes the second inequality strict, so a+b≥r+1. Opposite-part maximizers cover exactly a+b+1 vertices. This gives the near-balanced pair and, for k=ceil((s−r)/2), a seed of r+2 covered vertices followed by at most k−2 uncovered-vertex additions. The all-larger-to-smaller orientation supplies the remaining upper-bound case and the sharp lower bound. The question for literature review is whether an old theorem or an intermediate proof lemma already supplies this seed, making the rest a routine bridge. Elementary length itself is no adverse finding.

## New primary bodies obtained

Two lawful public author-deposited arXiv PDFs were downloaded on **2026-11-01 UTC / 2026-10-31 PDT**. Exact times, URLs, statuses, lengths and SHA256 values are in `retrieval-receipts.json`; extracted body texts are retained beside the PDFs (`.body`).

* **Caro–Henning, A Greedy Partition Lemma for Directed Domination**, [arXiv:1010.2467v1](https://arxiv.org/pdf/1010.2467v1), 12 October 2010, 12 PDF pages. SHA256 `e73b4cddc20d8c306343956fcd31c5b847a6f11195be596e46a3ea17907da681`. Corresponding journal citation: Discrete Optimization 8(3) (August 2011), 452–458, DOI 10.1016/j.disopt.2011.03.003.
* **Caro–Henning, Directed Domination in Oriented Graphs**, [arXiv:1010.2464v1](https://arxiv.org/pdf/1010.2464v1), 12 October 2010, 18 PDF pages. SHA256 `46a915ef6ca082b8709ba100a0e6810493b2ede1b70726cb90df665e90f68482`. Corresponding journal citation: Discrete Applied Mathematics 160(7–8) (May 2012), 1053–1063, DOI 10.1016/j.dam.2011.12.027.

Current arXiv abstract pages show only v1 for each. These are **actual original author proof bodies**, not quotations reconstructed from abstracts, but they are not authenticated final publisher PDFs. Both new publisher landing requests returned HTTP403 and were stopped; no alternate endpoint/proxy retry followed. University repository search returned metadata, not a separate manuscript, and reported a non-retryable robots restriction on uj.ac.za; no direct request to that route followed. The version limitation is retained explicitly.

## Greedy Partition Lemma: precise comparison

I read the definitions, Section 2's Lemmas 3–4 and their proofs, applications through Theorems 5, 7 and 10 and the Nordhaus–Gaddum section, and Section 3's multiple/distance domination arguments. These cover the original manuscript counterparts to chapter Theorems 54–58 and the potentially relevant selection machinery.

**Lemma 3, PDF p.4.** Its hypotheses are a hereditary class H of hypergraphs, integer t≥2, a positive nondecreasing continuous f:[t,∞)→[1,∞), and a property P. For every G∈H, small orders satisfy χ(G,P)≤|V(G)|, and orders at least t satisfy |V(G)|≥P(G)≥f(|V(G)|). Here P(G) is the maximum size of an induced subhypergraph having P and χ(G,P) the minimum number of P-parts in a vertex partition. Its conclusion is χ(G,P)≤t+∫[t,max(n,t)]1/f(x) dx.

The proof chooses a largest P-subgraph of order z≥f(n), removes it, applies induction, and bounds the integral over the final interval of length z below by z/f(n)≥1. It **consumes an independently supplied large-part lower bound**. It does not prove a bipartite opposite-part pair or the strict extra covered vertex. Giving it a property of domination by two centers and inserting the candidate's sharp bound as f would assume precisely the missing ingredient; that is not a subsumption deduction.

**Lemma 4, PDF p.5.** For integer k≥α(G), an orientation D, and an induced H of order n_H≥k and size m_H, it gives m_H≥n_H(n_H−k)/(2k) and Δ⁺(D_H)≥(n_H−k)/(2k). Its proof uses the Caro–Wei independence inequality and the total outdegree sum m_H. This is a **single global maximum**, not the two part maxima a,b. At K10,14, k=14 and n=24 give only Δ⁺≥10/28 (hence integer Δ⁺≥1), even weaker than the exact density bound Δ⁺≥6. Neither supplies coverage of 12 by two centers.

**Theorem 5, PDF pp.5–6.** It applies Lemma 3 with t=α and f(x)=1+(x−α)/(2α), using one-center out-neighborhood parts. It gives full domination at most α(1+2 ln(n/α)); the proof actually reaches α+2α ln((n+α)/(2α)) first. For (10,14), these real bounds are about 29.09 and 22.55 respectively, compared with the sharper known full-domination bound 14. A bound on the number of parts alone does not make two of those parts cover half. The lemma's induction retains no special opposite-part maximizers or the candidate's strict inequality.

Lemma 6/Theorem 7 concern complements of d-degenerate graphs and again use one global outdegree bound. For K10,14 the complement is K10 disjoint union K14 and needs d≥13; the theorem's t=27 already exceeds n=24, giving only the small-order branch of the general lemma. Theorem 10 requires K1,m-free graphs; here m must be at least 15, so its displayed bound with δ=10 is much larger than n. Their actual proofs do not contain an additional bipartite selection lemma. The remaining multiple-domination proof repeats full dominating sets in residual induced graphs; distance domination uses a semikernel and paths of length two. Neither changes to closed one-step majority coverage without an additional argument.

**Finding:** the inspected original greedy-partition body does not subsume the endpoint. This is a body/proof finding at the stated version, not a declaration that every conceivable application of an abstract partition lemma has been exhausted.

## Directed-domination manuscript: precise comparison

I read Sections 2–4, particularly the actual proofs of Lemma 3 and Theorems 2, 4–10 (PDF pp.4–8), and screened the remaining special-family/transversal sections and read the relevant degree/selection proofs in Section 6 (Lemmas 18–19, Theorem 20 and the multiple-domination construction). No pair-selection intermediate lemma matching the candidate was found.

**Lemma 3, p.5**, allows any covering V=union V_i by possibly overlapping vertex subsets and bounds full orientable domination by the sum of the full orientable domination numbers of G[V_i]. Its proof restricts an arbitrary orientation, takes a minimum dominating set in each restriction and unions them. It supplies no large covered subset for a fixed small number of centers unless such a subset is already known.

**Theorem 4(a), pp.5–6**, partitions along maximum-matching edges and leftover singletons. Each directed matching edge costs one center. **Theorem 5, p.6**, combines this bound Γ_d≤n−α′ with König–Egerváry/Gallai and Γ_d≥α to obtain Γ_d(G)=α(G) for every bipartite G. For Kr,s this is s. This is now a direct primary-proof comparison, extending the prior chapter-only comparison. The printed proof's reference to 4(b) should be 4(a); its displayed inequality and actual derivation are clear, and no new correctness audit is needed here.

For a partial-coverage adaptation, six disjoint edges already cover h=12 at (10,14), so this proof gives six centers. More explicitly, one can also choose any 12-vertex induced bipartite restriction and invoke Theorem 5; because each part is independent, its independence number is at least 6. Lemma 3 on such restrictions does not get two. The source's separate generic bridge from full domination s gives ceil(s/2)=7. Neither deduction reaches 2. These demonstrate failure of the specific natural bridges, not impossibility of all other arguments.

Theorem 6 groups color classes in pairs and invokes the same bipartite full-domination theorem; Theorems 8–10 use path or clique partitions. Section 6's Lemmas 18–19 bound low-indegree vertices via degeneracy/coloring, and Theorem 20 selects transversals of closed in-neighborhood hypergraphs after placing the low-indegree vertices themselves in the dominating set. None of these inspected proofs establishes a+b≥r+1 for nontrivial unequal bipartite orientations or its closed-pair coverage equivalent. Their full-domination bounds cannot themselves force a universally tiny full dominating set: the one-way K10,14 orientation has full domination number 14. A majority conclusion requires further coverage information; no complete old-to-new deduction was identified.

**Finding:** no subsumer found in the inspected directed-domination author body. A publisher-version-only added lemma has not been excluded.

## The 1996 paper: still materially missing

The actual **Chartrand–VanderJagt–Yue, Orientable domination in graphs, Congressus Numerantium 119 (1996), 51–63** was not obtained. Its complete-bipartite proof and neighborhood-selection/intermediate upper-bound lemmas therefore remain unread. The chapter and Anderson et al. body already inspected in r1 do not fill this gap.

New discovery routes, rather than repeating r1's failed publisher search/volume requests, were: public arXiv title discovery (successful for the two Caro–Henning bodies); author/university-repository and dissertation searches for the 1996 authors/title; an Internet Archive public catalog query for the journal and year; and an OpenAlex location-discovery query for the exact paper title. The Archive response has zero matches **for that catalog query only**. The top-ten OpenAlex search returned related works but no authenticated exact 1996 record or body location. Author/dissertation searches located bibliographic references and a differently titled 1995 thesis, not the target paper. No account, loan, purchase, contact, hidden endpoint or access-control bypass was attempted. Search queries/results where saved are in `search-primary.json` and `search-archive-author.json`; other focused batches are recorded in `search-log.json` with findings and transcript-only status. HTTP discovery bodies/receipts are retained. No inference that the paper is unavailable everywhere is made.

I did not re-request the r1 publisher 404 route, the inherited MathDB403, or any denied new route. The bounded new routes have yielded useful bodies and then diminishing returns; further speculative URL loops are unwarranted. **Missing-source clearance is not established.** The precise decisive remaining object is the 1996 full proof, plus any final-version additions to the Caro–Henning papers; metadata and full-domination theorem statements cannot exclude an intermediate lemma that supplies the candidate's entire pair seed.

## Verdict, chronology and limits

No exact existing theorem plus routine bridge subsuming the full endpoint has been demonstrated. Accordingly a novelty FAIL would overstate this record. The new proof comparisons narrow the previous HOLD, but do not remove its central 1996 objection. Qualified novelty and final significance clearance therefore remain **HOLD**, with **intrinsic significance PASS conditional on novelty**, as in r1. The full sharp two-parameter minimax family remains potentially substantive; no new-method claim is justified by its elementary averaging step.

I reuse r1's contemporary Palomar receipts from 2026-11-01 05:05 UTC (revision 651, release ff01fa2bd3240170cedf26fba4b146111e3b132a8c11fe533e5cea0a9fe75287; exact majority-out-domination and bipartite-domination queries empty) and the author's 04:43–04:48 UTC OpenAI math head/tree receipts (head 4eaee87548250b2682affda7d05d947c05554bae, head dated 2026-10-30; untruncated preprints subtree separately obtained). These are bounded metadata/path screens, not theorem-body clearance. The new sources predate the conjecture and provide no later resolution that warrants another immediate registry request. The same-day author upload of the candidate is not public priority evidence. No worldwide priority, complete citation coverage, non-English literature sweep or MathSciNet/zbMATH clearance is claimed.

Actual credit remains zero for this candidate, conditional credit at most one family, and root alone accepts. No credit attaches separately to formalization, degree bounds, augmentation or a parameter instance. Existing source/math/Lean correctness PASS is preserved; a paper and root acceptance remain outside this review.
