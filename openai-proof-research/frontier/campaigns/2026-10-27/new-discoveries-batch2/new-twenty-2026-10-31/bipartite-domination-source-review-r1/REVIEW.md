# Independent review: MathDB 370334

Decision: ordinary refutation PASS; literal historical binding PASS; new-discovery significance FAIL by complete prior-theorem bridge. Recommend no Pi execution for discovery credit. Accepted campaign count remains 52/60, contribution credit 0. No Lean, acceptance, publication, contact or execution authorization is supplied by this review.

## Scope and frozen boundary

I read the entire TASK.txt, all applicable ancestor AGENTS, the entire r307/ORDINARY-PROOF-HOLD.md, and the full raw provenance/370334.jsonl. Before any author mathematical reads I verified all 142 paths in frozen-inputs.json against SHA-256: all matched (frozen-before.json). The final verification is in frozen-after.json. Work is confined to this lane. Historical scanning used only the exact supplied historical-results-allowlist.json; paths containing crown were skipped without reading or hashing. There were no children, git operations, Lean runs, mathematical enumerations, solvers, numerical searches, shared or author writes, browser/account actions, installations or external messages. Network operations were public read-only research.

## Literal statement and all-version source review

The frozen raw record states that every k-regular bipartite G with sides A,B of size n satisfies gamma(G) <= 2 ceil(n/k), and rho_G <= ceil(n/k)/n. Its source is Hosking arXiv:2509.10473; the record is marked open with no solutions, created 2026-08-11, lastmod 2026-10-29. These are record facts, not novelty evidence. Division by k presupposes k>0; this review uses k=15, so does not exploit an undefined zero-degree endpoint.

I inspected the actual frozen HTML-derived bodies for v1,v2,v3,v4 and the unversioned body identified as v5, including their definitions, regular/degree passages and the relevant section context. Frozen HTML preserves formulas if prose extraction is ambiguous. The arXiv submission-history dates are v1 2025-08-26, v2 2025-09-16, v3 2025-10-25, v4 2026-02-28, v5 2026-08-23 (UTC; exact times in the frozen abs body). The manuscript-internal v1 date and submission date differ; submission history is the version chronology used here.

* v1 Section 5 and v2 Section 5 concern connected regular graph PAIRS and a k>=32 sufficient regime for Vizing, using a harmonic-number domination upper bound. Neither supplies the historical balanced bound under review. This review does not endorse or audit those unrelated Vizing proofs.
* v3 Section 2 globally specifies finite simple graphs and rho_G=gamma(G)/|V(G)|. Section 3 has connectedness assumptions in individual results, not a global high-degree restriction. Section 4 explicitly introduces a regular bipartite graph with equal side sizes n, then Conjecture 1 quantifies over EVERY such graph and states both exact raw-record inequalities. There is no k>=32, k>=7, n=k+r with small r, matrix-rank, or packing-existence hypothesis attached to Conjecture 1. The claimed packing intuition is motivation, not an assumption that can silently narrow it.
* The k>=7 discussion and thresholds in v3 concern the conditional consequences for Vizing. Corollary 2 assumes Conjecture 1 and derives size thresholds for graph pairs. The subsequent small-r results do not restrict the preceding conjecture. For our witness n=28,k=15,r=13; no small-r specialization is being claimed. Even if connectedness were imported, the explicit witness is connected, as proved below.
* v4 and v5 replace the regular-conjecture discussion with imbalance/leaf-deletion material. Their Conjecture 1 is Vizing's Cartesian-product conjecture, not the separate proposed domination bound. No occurrence of the old regular ceil-bound or a correction explaining its disappearance was found in those bodies. Removal by v4 is not evidence of a proved resolution. The current abs retrieval is byte-identical to the frozen abs and still advertises v1-v5; no journal reference for Hosking was identified in the checked metadata. No independent journal/appendix resolution was established.

The historical assertion is therefore accurately targeted. Refuting it does not refute Vizing's conjecture. The raw record's current-open wording cannot be adopted as the author's current position after v4/v5 omission. Full latest-state literature clearance remains unavailable; the new-discovery exclusion below does not depend on that clearance.

## Independent ordinary proof of the explicit counterexample

Let U={0,...,7} and P={S subset U: |S|=2}. Take vertices {A,B} x P. Adjacency holds precisely between opposite sides with disjoint pair labels. This relation is symmetric because disjointness is symmetric. It has no loops because sides must differ; no multiplicities occur because adjacency is a relation. Thus it defines a finite simple undirected bipartite graph. Each side has C(8,2)=8*7/2=28 vertices, total 56. For a vertex labelled S, opposite neighbours correspond bijectively to pairs of U minus S, a six-element set. Degree is C(6,2)=6*5/2=15 on both sides, with no additional neighbours.

Connectedness can also be proved without a search. Any two same-side labels S,T have a common opposite-side neighbour Q: |S union T|<=4, so its complement has at least four elements, from which a pair Q exists. For vertices on opposite sides, choose any neighbour W of the first, using degree 15>0; W and the second are on the same side and have the preceding path of length at most two. This gives a walk of length at most three. A finite walk contains a path after deleting repeated segments. The graph is connected and has more than one vertex.

Ordinary domination means every vertex belongs to D or has a neighbour in D. Suppose D dominates and |D|<=4. Write X,Y subset P for the selected labels on sides A,B. The two disjoint vertex types give |D|=|X|+|Y|. Side exchange is an automorphism, so assume |Y|<=|X|; hence |Y|<=2. Every A-side pair meeting every member of Y has no selected opposite neighbour, so must itself be in X. Same-side selected vertices other than itself cannot help.

If |Y|=0, this forces all 28 A labels into X, contradicting |X|<=4.

If |Y|=1, write Y={{a,b}}. The seven labels {a,c}, for c in U minus {a}, all meet {a,b}. They are distinct: removing a recovers the singleton {c}. Thus seven labels must lie in X, whereas |X|<=3. This includes c=b and requires no avoidance of selected labels: being forced into X is the contradiction.

If |Y|=2, its distinct members T1,T2 either intersect or are disjoint, and |X|<=2. In the intersection case choose a in T1 intersect T2; the same seven distinct pairs containing a meet both. In the disjoint case take the four labels {a,b} for (a,b) in T1 x T2. They meet both. They are four distinct pairs: intersecting a label with T1 recovers {a}, and with T2 recovers {b}. Consequently four labels must lie in X, contradicting |X|<=2. No arbitrary-choice collision remains in either family.

These cases exhaust |Y|<=2. There is no dominating set of size <=4. The full finite vertex set dominates, so the nonempty finite collection of dominating-set cardinalities has a minimum gamma(G); the preceding argument gives gamma(G)>=5. It proves the actual universal-statement negation, not total domination, independent domination, beta, a proxy or a helper endpoint.

Because 15<28<=30, ceil(28/15)=2 over the rationals/reals; thus 2 ceil(28/15)=4<gamma(G). By v3's definition rho_G=gamma(G)/56, it is at least 5/56>4/56=1/14=ceil(28/15)/28. More generally for n>0, dividing or multiplying gamma <=2 ceil(n/k) by the positive 2n proves exact equivalence to the density bound. Neither exact gamma nor smallest-witness status is needed or asserted. No enumeration was used.

## Prior bodies: exact-family and invariant distinctions

Complementing the B label T maps it to the six-subset U minus T. Then S intersect T is empty iff S subset U minus T. This is exactly H(8,2) in Kumar-Kumar Definition 2.2, and is the bipartite double of KG(8,2).

The frozen Kumar-Kumar journal body was actually read at Definition 2.1(v),(vi),(ix), Definition 2.2, Theorem 1.2/Corollary 4.3 and Proposition 4.2 with proof. Their nu is induced-matching number; beta maximizes the size of independent minimal vertex-wise dominant sets, defined by intersection with every closed edge neighbourhood. They are not ordinary gamma. A large induced matching alone cannot supply gamma>4: vertices outside its induced endpoints can dominate several endpoints. Proposition 4.2 is an upper beta bound. No conversion yielding the required ordinary lower bound was demonstrated. It is not a subsumption certificate.

The actual Ivančo-Zelinka 1993 body (pp.147-152) was retrieved from DML and read at graph definitions, Theorem 1 and proof, and Theorem 3 and proof. The results concern KG(n,2), not its bipartite double. For KG(8,2) the ordinary and total domination numbers are 3. Projection from a double only gives gamma(double)>=gamma(base)=3, which is insufficient here. The classification of dominating triples is relevant combinatorics but is not by itself a cited theorem giving gamma(H(8,2))>4. The scan's OCR has errors; the conclusion at n=8 does not depend on its garbled low-n symbols.

Gorodezky's 2007 Waterloo thesis was obtained from the native institutional item's advertised download (the server redirected automatically to its content URL; no API URL was manufactured). I read the actual sections 4.2, Theorem 4.2.1 with full proof and Corollary 4.2.2, and sections 7.2-7.3 definitions/theorems/proofs on q-Kneser domination. The k(k+1) threshold at k=2,n=8 gives ordinary KG domination 3, not the bipartite lower bound 5. Its q is a prime power and its vertices are subspaces; q=1 is not a valid finite field substitution. The thesis does not license silently treating its incidence graph I(n:k) as H(n,k); its incidence sides are points and k-subsets, with unequal sizes. Only targeted relevant sections were read, not a complete thesis audit.

Clark-Shekhtman's original q-analogue bipartite body remains a material exact-family source gap. CiteSeer returned 403; an author-uploaded ResearchGate entry was found, but its actual PDF link returned 429. Neither was retried. The thesis's account of q-Kneser results cannot substitute for that unread bipartite section. No exact earlier H(8,2) witness is established. This gap prevents exact-family clearance, but does not prevent exclusion by the independent complete generic bridge below.

## Decisive complete generic subsumption bridge

Primary body: Michael A. Henning and Paul Horn, Optimal linear-Vizing relationships for (total) domination in graphs, author institutional copy https://cs.du.edu/~paulhorn/pap/vizing.pdf, Section 4, Theorem 16, printed pp.11-15 including Claim 4 and Lemma 5. I read the actual ordinary-domination statement and its surrounding proof and finite-existence application, not merely its total-domination title. Theorem 16 asserts: for sufficiently large fixed integer d, put c_d=ln d -4 ln ln d. For a uniform simple d-regular graph F of even order N, the probability gamma(F)<floor(c_d N/d) tends to zero as N tends to infinity through even integers. In particular, for arbitrarily large finite even N there exists such F with gamma(F)>=floor(c_d N/d). This is exactly the finite consequence explicitly used in Lemma 5. The proof uses random matching models and a first-moment estimate; I ran no random experiment or enumeration. I rely on the published theorem, not a new probabilistic conjecture.

Here is the full transfer to the literal regular balanced bipartite class. Fix an integer d above the theorem's unspecified finite threshold and large enough that c_d>2, possible since ln d -4 ln ln d tends to infinity. Choose a sufficiently large even N>d satisfying (c_d-2)N/d>3, and large enough that the theorem's good-event probability is positive. Such even N exist; dN is even and the simple d-regular model is nonempty for N>d. Select one finite simple d-regular F guaranteed by the theorem. Define B(F) on {0,1} x V(F) by (0,u) adjacent to (1,v) iff uv is an edge of F. It is finite, simple, undirected, bipartite, has side sizes N,N, and degree exactly d (neighbour labels correspond bijectively to neighbours in F).

If D dominates B(F), project its labels to S subset V(F). For u outside S, (0,u) is not selected, so it has a selected neighbour (1,v) with uv an edge. Thus every u outside S has a neighbour in S: S dominates F, and |S|<=|D|. Minimum existence gives gamma(B(F))>=gamma(F). This is a complete ordinary-domination bridge; a nonbipartite theorem alone would not suffice.

The floors and ceilings now give

    gamma(B(F)) >= floor(c_d N/d)
                 >= c_d N/d - 1
                  > 2N/d + 2
                 >= 2 ceil(N/d).

The strict inequality uses exactly (c_d-2)N/d>3. Therefore an actual finite graph in the raw record's class violates its bound; its normalized inequality fails by division by 2N. No asymptotic symbol is being compared heuristically with a finite ceiling. The double need not be connected, which is allowed by the literal universal claim and by v3's global assumptions; connectedness of the separate 56-vertex witness has already been proved. The theorem is an actual ordinary-gamma lower bound, not an induced-matching/beta or total-gamma substitution.

Chronology: the author's page links this exact preprint; the University of Johannesburg institutional publication record identifies the work as Journal of Graph Theory 106(1),149-166, May 2024, DOI 10.1002/jgt.23070. A 2023 university conference page independently advertises the same authors/title and result. The 2024 publication predates Hosking v1 (August 2025), the bound's actual v3 assertion (October 2025), the MathDB record (August 2026) and this campaign. The institution's publication metadata was readable through web search/open; a subsequent direct HTTP capture returned 403 and was not retried. No Wiley body route was accessed. The author copy is a preprint, not represented as a byte-verified journal version; theorem numbering here is that copy's numbering.

This complete earlier theorem plus elementary double-cover transfer already refutes the exact universal claim. Under the campaign's explicit rule excluding known-result corollaries, the new-discovery significance gate FAILS. This conclusion does not assert that Henning-Horn mention Hosking or the exact 56-vertex graph. No exact earlier witness is required by the rule. The finite witness is useful exposition/formalization material but cannot restore discovery credit merely by being small or readily formalized.

## Current bounded registry and access limits

Fresh public HTTP snapshots checked LeanPool main head 55b1badf31a1a5eb2f5c11f3334e6bd72a5c6ff2 and its pinned candidates directory; OpenAI/math head 4eaee87548250b2682affda7d05d947c05554bae; Omega/trureturing dev Problems head 074df09ddbbef1843ddb383577bfaa827f753e36. The last differs from r307's 0a4725248d4eaad1b6c77d670c2dbc331028f445. Visible files/views did not contain target ID, arXiv ID, Hosking or Kneser. Frozen r307 candidate/import/catalogue and registry receipts were consulted as bounded routing, not proof clearance. No current matching theorem endpoint or matching project chronology was established; directory snapshots are partial and repository heads are not per-result publication dates. No claim of exhaustive registry coverage is made. Exact allowlisted historical metadata has no prior literal 370334/Hosking duplicate apart from r307's own held investigation; Kneser term hits concern unrelated homology, coloring and Hamiltonicity problems (history-review.json).

Known denied MathDB/Palomar-recent/GitHub API/Togni/Wiley/previous IEEE-DOI routes were not attempted. Search engines sometimes returned Wiley indexed metadata without a page request; these were not treated as body access. Newly failed CiteSeer 403, ResearchGate PDF 429, author research.html 404 and direct institutional-publication 403 were not retried; no TLS changes, proxy/auth alterations, account actions or access-control bypass was used. The successful advertised Waterloo download's automatic redirect is documented in its receipt. The DML copy is for private research with its original terms retained; no claim of OA or redistribution permission is made for automatically served journal HTML. The source files stay in this assigned private lane.

## Gates and recommendation

* Literal historical binding: PASS; latest-open-status inference: NOT CLEARED.
* All frozen Hosking version contexts: PASS for targeted assumptions/removal comparison; unexplained removal is an explicit limit.
* Full ordinary mathematical refutation, finite minimum and rho bridge: PASS.
* Exact H(8,2) prior-body completeness: HOLD, with the original q-bipartite section still unread.
* Generic universal-claim subsumption: DEMONSTRATED by the full bridge above.
* Bounded novelty: not exhaustive; a positive new-discovery claim is excluded regardless of remaining gaps.
* Significance for this campaign: FAIL, known-theorem corollary.
* Pi recommendation: DO NOT ROUTE this as a new discovery. If the parent separately wants an educational formalization, it needs its own authorization and receives zero discovery credit. No Pi work was started or authorized here.

The author needs no mathematical repair to the explicit witness. The material correction is to qualification: retain the ordinary proof but replace the unresolved generic-subsumption question with the precise exclusion above. Only the parent may integrate this review; no author files were changed.
