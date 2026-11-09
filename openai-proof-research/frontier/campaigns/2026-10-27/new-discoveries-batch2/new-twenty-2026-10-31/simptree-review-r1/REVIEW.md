# Independent adversarial review: MathDB 369935

Recommendation: **EXCLUDE from campaign credit; do not invest in Lean acceptance packaging.** The witness is a valid ordinary counterexample, but it is a short augmentation of a printed obstruction. Root alone decides acceptance. This review does not claim a previously published refutation or worldwide priority.

| Gate | Verdict | Reason |
|---|---|---|
| A | QUALIFIED_PASS | Literal v1 counterexample survives; later versions change definitions and strengthen the hypothesis, rather than merely renaming it. |
| B | PASS | Independent exact enumeration, counting, connectivity, ordering search, and structural proofs agree. |
| C | FAIL | Mandatory citing-work and current candidate-body clearance remains incomplete after access denials. No public exact refutation located in the bounded accessible screen. |
| D | FAIL | Explicit cone of the printed four-triangle obstruction, four elementary facet attachments, and one disjoint simplex give exactly this witness. |
| E | QUALIFIED_PASS | A literal, small-certificate route exists, but no Lean certificate is checked here. |

## A. Statement and version fidelity

All line references below are original text-file lines, preserved in `evidence/v1-numbered.txt`, `v2-numbered.txt`, and `v3-numbered.txt`. `evidence/SOURCE-QUOTES.md` contains verbatim, line-numbered quotations of each version's definitions and target, including all circuit restrictions and the preceding theorem. Full source texts are retained alongside the excerpts. The original PDFs and their HTTP receipts are hash-bound in `inputs-before.sha256`.

Correct attribution: v1 (25 August 2025), *Characterisations and Structural Properties of Pure n-Simplicial Trees*, has **Gaurav Kottari, Niteesh Sahni, and Qazi J. Azhad**. V2 (22 February 2026) has the same three authors and the title *Structural Characterisations of (n−1,n)-Trees*. V3 (1 August 2026) has **Gaurav Kottari and Niteesh Sahni** and the latter title. The live arXiv abstract's submission history still ends at v3 (`downloads/arxiv-current/body`, lines 112 and 165–170). There is no withdrawal notice there. The cached v3 PDF receipt identifies `2508.17854v3.pdf` in Content-Disposition.

The source uses **nonempty** faces. Every singleton of V belongs to K; pure means every face is contained in an n-simplex. Alpha_k counts faces with k+1 vertices. Thus p counts all vertices of K, not just the largest connected component; there are no ghost vertices. See v1:120–132, v2:144–158, v3:135–149. A formal encoding that includes the empty face must explicitly bridge this harmless difference, or exclude it directly.

Walks alternate m-faces and n-facets, with distinct consecutive m-faces both contained in the intervening facet. A path has all simplices distinct; connectedness is path existence between every pair of m-faces. A circuit closes its first face and has pairwise distinct m-faces before closure and pairwise distinct n-facets (v1:159–178, v2:206–233, v3:200–228). Length one is impossible because the walk requires distinct consecutive faces. Length two is allowed for circuits. Source connectedness means (n−1,n)-connectedness (v1:241–243; v2 connectivity discussion; v3:278–286).

V1 Definition 4.1 (360–372) requires r≥3, the initial face absent from **each** internal facet, and the internal transition m-faces contained in **distinct** common ridges. A simplicial cycle is the closure of those facets. Acyclic means no such cycle, at any m (414–415). Definition 5.1 (517) says a simplicial tree is connected and acyclic. V1 Definition 2.4 (145–149) defines a complete ordering by each new facet's entire attachment being a full simplex on m+1 vertices, not just by sharing a ridge. Theorem 5.4 (702–705) identifies trees with (n−1)-complete orderings.

V2 Definition 3.8 (556–570) changes “each” internal facet to **some**, and drops distinctness of transition ridges. V3 Definition 3.9 (618–628) retains these changed restrictions and calls them **Dewdney cycles**. In v2/v3 the tree term in the target is the ordering-defined (n−1,n)-tree (Definitions 2.4–2.5); connected-and-acyclic is an equivalent characterization (v2 Theorem 4.1, 642 onwards; v3 Theorem 4.1, 731 onwards), not the v1 definition reused without change.

The targets are quoted exactly in the appendix: v1 Conjecture 6.1, 973–982; v2 Conjecture 4.10, 1079–1089; v3 Question 4.11, 1201–1211. Their preceding results are respectively Theorems 5.12 (915–923), 4.9 (1034 onwards), and 4.10 (1158–1167). The preceding result fixes the ridge count alpha_(n−1)=n(p−n)+1; the target allows an intermediate k. V1 asks for absence of **simplicial cycle sequences** for some m. V2 and v3 instead require absence of **circuits** for some m, a stronger condition. V3 asks only the difficult implication, and explicitly says the question remains open. It does not announce a counterexample, withdrawal, or solution. Calling all changes merely a rephrasing would be inaccurate; this witness nevertheless satisfies the stronger circuit condition with m=2 and refutes both versions.

The MathDB literal (`../expanded-corpus-r212/raw/369935.jsonl`, line 1) agrees with v1's quantified display, but its explanatory sentence incorrectly calls the replaced condition “top-dimensional”: the top count is retained and the **ridge** count is relaxed. The record also mixes current authors/title with v1's statement. These bibliographic/explanatory defects do not defeat this n=3 witness. The n=1 empty range for k is an endpoint defect, not the basis of this review or its recommendation.

## B. Independent mathematics

I wrote and ran `scripts/check.py` with Python isolation and the resource wrapper; no discovery script was imported or executed. The complete replay is `scripts/replay.sh`; `logs/math.log`, `logs/replay.log`, `evidence/math.json`, and `evidence/connectivity.json` retain outputs. Facet indices are 0–8 in the assigned order.

The nonempty downward closure has f-vector **(12,30,29,9)** and is pure of dimension 3. For k=1, the required edge count is 9·3+3=30, and 9=12−3. For k=2 the requested value is 28, whereas the actual value is 29. Every connectivity relation m=0,1,2 has exactly the two facet components {0,…,7} and {8}. In particular it is disconnected in the exact source sense. The ordering dynamic program checks all reachable prefix subsets, with the entire attachment required to be one full triangle; no complete facet ordering exists.

For an independent enumeration of **all** circuits, the code enumerates all simple cycles of the bipartite m-face/facet incidence graph, rooted at the least face and with first facet index less than last facet index. This counts each circuit once up to cyclic rotation and reversal, not every spelling of a sequence. It tests **every root rotation** for each version's cycle restrictions, including a distinct-ridge matching search for v1. Enumeration digests, length distributions, and example sequences are retained in `math.json`.

| m | Circuits by length r: count | v1 cycles, modulo rotation/reversal | v2/v3 cycles, same convention |
|---|---|---|---|
| 0 | 2:36, 3:151, 4:586, 5:1670, 6:3101, 7:2841, 8:767 | 4:28, 6:37 | 4:28, 5:37, 6:53, 7:71, 8:20 |
| 1 | 2:24, 3:49, 4:154, 5:443, 6:1165, 7:1870, 8:1178 | 4:42, 6:135 | 4:42, 5:67, 6:249, 7:332 |
| 2 | none | none | none |

Consequently the complex is **not acyclic in the source's unqualified sense**: it has lower-dimensional simplicial/Dewdney cycles. It satisfies the target's existential absence condition at m=2. One v1 cycle has vertices 0,1,3,5,4,7 and facets 0,2,3,4,5,6, then returns to vertex 0. This distinction must appear in any subsequent paper.

The least-facet proof is exact and independent of enumerating cycle lengths. For i=0,…,8, the only possible triangle shared with a later facet is respectively 123,123,135,156,145,147,047,none,none. In a circuit, its least-indexed facet has two larger neighboring facets and two distinct incident triangles. Both triangles would have to equal the unique triangle in this list, a contradiction. This proves absence of every (2,3)-circuit and hence every relevant cycle.

Disconnectedness is essential, in **all** sizes: ridge-connected facets admit a ridge-adjacent enumeration. The first facet has n+1 vertices and each later facet introduces at most one new vertex. If t=p−n, equality p=n+t forces each later facet to introduce exactly one new vertex. Its other n vertices are precisely its common ridge with an earlier facet. Every old face of this new facet lies in that ridge, so the entire attachment is its full downward closure. This is a complete ordering. No acyclicity or intermediate count is needed for this connected case.

Small exhaustive checks independently corroborate this: for dimension 2 and p=3,4,5, respectively 1,6,100 full-support families with t=p−2 were tested; 1,6,70 met connectedness and intermediate counts and all had complete orderings. In dimension 3, p=4,5,6 gave 1,10,395 full-support families; 1,10,200 met those conditions and all had complete orderings. These are deliberately small screens, not minimality claims.

Dimension 2 cannot supply a target counterexample: the only intermediate index is already k=n−1, so the target is precisely the preceding theorem, as v3 itself notes (1198–1199). For m=1 one can also see this from the ridge incidence forest identity e=2t+c: the two counts force c=1, hence connectedness and the ordering argument above. For m=0 the source's cycle/circuit lifting results reduce to the ridge case (v1 Corollary 4.8; v3 Lemma 4.9). No stronger independent general lifting lemma is claimed by the finite screen.

## C. Bounded prior-art screen and access limits

The live arXiv page confirms v3 remains current. Exact-ID/counterexample, author-pair, Dewdney, Faridi, and homological-tree searches are saved in `evidence/web-search*.json`. No exact public refutation surfaced. Search results are discovery aids, not proof-body clearance; indexed excluded-host hits were not followed or relied upon.

OpenAlex returned **429** on the first work-search request, before a source work ID or citing list was obtained. No retry or further OpenAlex request was sent; the planned author query was locally blocked. Therefore **the citing-work review is missing**, not negative. See `downloads/openalex-source/receipt.json` and `logs/fetch.log`.

Lean Pool current HEAD was successfully retrieved as **01db1d7049cf9668bda1e9e106875ee1278b43e6**, with commit date 7 October 2026. `LeanPool/projects.yml` was fetched and screened for 369935, 2508.17854, Kottari, Sahni and related tree terms; no matching target found. This HEAD file request was not pinned, so it is not asserted to be a transactional snapshot of that commit. The `candidates/` API returned **403** with exhausted rate limits. No subsequent api.github.com request was sent. Both planned repository searches were locally blocked: **zero unauthenticated GitHub search queries actually sent in this review**, within the eight-query cap. Discovery-lane cached pool candidate metadata is hash-bound but does not replace the missing current candidate-body review. All HTTP responses, errors, headers, timestamps, and body hashes remain in distinct download directories; none was overwritten.

Classical distinctions matter. Faridi/Caboara/Selinger's notion is based on facet leaves/cycles; Kalai's hypertrees and the Duval–Klivans–Martin spanning-tree theory use homology and skeleton conditions. The source's own v3 appendix explicitly distinguishes these notions (1223–1264). The author-hosted CFS paper and DKM papers/survey were located in the saved searches; the DKM survey places Bolker, Kalai and Adin in the homological lineage. Their generic statements about counts or acyclicity cannot be substituted for a refutation of this particular Dewdney-ordering question. I did **not** finish primary-body audits of every classical paper or enumerate all coauthor publications. Searches for the author pair surfaced this source but no independently verified resolving companion paper. This is an access- and coverage-limited failure to clear Gate C, not evidence that no such paper exists.

No Crossref, Semantic Scholar, arXiv search API, ScienceDirect, or DBLP request was intentionally made. No challenge was bypassed, TLS verification disabled, denied-host redirect followed, or author contacted. General web search does not supply HTTP transport headers; those results are separately retained as tool-result receipts, not represented as raw HTTP receipts.

## D. Printed constructions and exclusion

The complete figure/example inventory is as follows; proof-internal dummy complexes are not additional printed constructions.

- All versions: Figure 1 has facets 123,234,456,789,89(10),78(10), with components {456}, {123,234}, and the last three facets (v1:190–201,253–259; v2:248–264; v3:291–304). It also supplies reduced-path and cycle illustrations in the adjoining text.
- V1 Figure 2(a),(b) prints genuine simplicial trees, with (p,e,t)=(6,9,4) and (5,7,3) (519–528). These have the usual t=p−2. They are not connected acyclic exceptions to that count.
- V1 Figure 3; v2 Figure 2; v3 Figure 3: facets **123,234,345,145,126,137,149,158** (v1:687–699; v2:888–899; v3:965–977). They are ridge-connected and ridge-circuit-free, but cyclic at m=0; thus they are not globally acyclic. Their first four facets are the obstruction core used below. Geometrically this is a reused-vertex/vertex-identification mechanism: 123,234,345,456 with vertex 6 identified with 1 gives 123,234,345,145. No claim that the authors explicitly use that phrase is needed.
- V1 Figure 4(a); v2 Figure 3; v3 Figure 4: disconnected pure 2-complex with p=6,e=9 and no ridge circuit; v3 gives facets **123,256,345** (v1:899–908; v2:1018–1027; v3:1098–1126). It defeats the older Dewdney conjectures, but has t=3 rather than p−2=4.
- V1 Figure 4(b); v2 Figure 4; v3 Figure 5: disconnected p=6,t=4 ridge-circuit-free example, explicitly **124,123,235,456** in v3 (v1:950–953; v2:1041–1043,1069–1074; v3:1154–1155,1186–1195). It has 11 edges, missing the required 9. The authors already note that dropping the intermediate/ridge count allows disconnected examples, but do **not** say their printed example meets both counts.
- V2's unnumbered T1,T2,T3 (519–548), retained in v3 (582–613): **123,135,156,345**; **123,234,245**; **123,234**. They explain why unrestricted lower-face circuits, endpoint ambiguity, and length-two circuits must be distinguished from cycles. They are genuine ordering trees, not globally acyclic count exceptions.
- V3-only Figure 2 (523–526,556–557): **123,234,345,456,567,678,378,389**, a connected example lacking the proposed reduced vertex path from 1 to 9. It uses a recycled vertex and is another warning against conflating ridge-circuit-freeness with all cycle-freeness.
- V3-only Figure 6(a),(b), appendix 1236–1264: H1 has maximal facets **123,234**, a Dewdney tree lacking a full edge skeleton; H2 has maximal facets **123,234,45**, a nonpure Faridi example taken from CFS. These do not directly supply the witness.

There cannot be a connected globally acyclic example with t≠p−n under the source's tree equivalence and counting theorem. The pertinent printed exceptions are connected **ridge-circuit-free but lower-cyclic** examples, and disconnected examples. The candidate shares exactly this mechanism.

Here is the decisive **exact** augmentation, verified by assertions in `scripts/check.py`:

1. Take the four-triangle subcomplex **123,234,345,145** printed as the first four facets of v1/v3 Figure 3 (v2 Figure 2).
2. Relabel its vertices by **1→6, 2→5, 3→1, 4→7, 5→0**, and cone with new vertex **4**. The tetrahedra are exactly **1456,1457,0147,0467**, candidate facets 4–7. Their f-vector is (6,14,13,4).
3. Attach **1356** along 156 with new vertex 3, then **1235** along 135 with new vertex 2. The f-vectors become (7,17,16,5), then (8,20,19,6).
4. Attach **1234** and **0123**, both along 123, reusing existing vertices 4 and 0. Each adds two edges and three triangles, with no new vertices. The vectors become (8,22,22,7), then (8,24,25,8).
5. Take the disjoint union with **89AB**, giving exactly (12,30,29,9) and the assigned nine facets.

This is not an isomorphism claim about the **entire** printed eight-triangle figure, nor a claim that merely coning Figure 5 suffices. It is an explicit cone of its printed obstruction **subcomplex**, followed by four elementary ridge attachments (two recycled vertices) and a disjoint simplex. The edge/top count tuning is transparent: the eight-facet component has t=p and e=3p; a disjoint tetrahedron converts these to t=p−3 and e=3p−6. Circuit-freeness is preserved by the displayed one-later-ridge elimination list.

Dimension 3 is the first nontrivial dimension for the question, and nine facets give a compact exact refutation. Those are positive mathematical features. Nevertheless, under this campaign's express exclusion of short augmentations/reuse of printed obstruction mechanisms, the cone and elementary attachments above are insufficiently independent for discovery credit. That is the reason for **EXCLUDE**, independently of the incomplete Gate C screen. No minimality or complete classification of possible augmentations is claimed.

## E. Cheapest literal Lean endpoint, if root nevertheless continues

Use a finite vertex type and `Finset (Finset V)` of **nonempty** downward-closed faces, pure by containment in a facet of size n+1. Define alpha_k by cardinality filtering, with p=alpha_0 and every vertex represented. Keep all nonempty facets explicit. Define walk/circuit sequences by a length r and indexed finite functions for faces/facets, separate injectivity predicates, and incidence/closure constraints. Define v1 simplicial cycles with its universal internal-endpoint exclusion and distinct transition ridges. Define connectedness by exact (n−1,n)-path existence between distinct ridges (zero-length self paths handled explicitly), and `SimplicialTree := Connected ∧ Acyclic`. Define complete attachment and ordering separately rather than using the desired equivalence as an axiom.

The literal conjecture is a proposition universally quantified over n≥1, finite p, and pure K: `SimplicialTree K ↔ (∃ m<n, NoSimplicialCycle K m n) ∧ (∃ k, 1≤k ∧ k<n ∧ alpha K k = (p-n)*choose n k + choose n (k+1)) ∧ alpha K n = p-n`. Its negation follows by instantiating n=3, p=12 with the explicit witness, proving the RHS and disconnectedness. Do not replace its cycle premise by an unrelated graph predicate without a proved semantic bridge. For v3, state a second proposition with circuit-freeness and the ordering conclusion.

The kernel-cheap route is a general **least-facet** lemma on injective circuit indices, proved with a minimum in a finite image. Bridge an arbitrary n-simplex of the downward closure to one of the nine generators by equal-cardinality containment. Supply 36 small facet-intersection facts and small face-list cardinality certificates, rather than reducing a large powerset expression or searching permutations in Lean. A vertex-block invariant proves every path stays on one side of {0,…,7}/{8,…,11}. This directly defeats connectedness without formalizing the ordering DP. The quantified definitions and bridges are the substantive cost; do not certify only an abstract graph.

Use Lean 4.34.1 with pinned mathlib d13f23b723b8a846827a245b89c10fc7d3f11612, `-j1 -M3500`, the RSS/CPU/wall wrapper, and lane-local artifacts. Prefer small separately proved equalities to large interpreter evaluations; avoid native_decide and opaque computation axioms. Audit transitive axioms and perform a fresh extracted replay if pursuing acceptance. No Lean process was run here, no discovery Lean attempt is treated as checked, and no kernel-cost guarantee is made. Gate E is a feasibility assessment only.

## Integrity and replay

`evidence/inputs-before.sha256` and `evidence/inputs-after.sha256` are byte-identical manifests covering **all files** in the discovery lane and root-check lane. Their SHA256 is **fb969596e57cfcbe16836e3738203f3a5ed5230138dc925096efdd9e09c708b0**. The candidate hash matches the assignment: **c49485b160436a7ef5211b7949f9ae3feb496317e8018bf8b1a44d1e8e20a407**. The replay verifies every manifest entry before and after computation. Source bodies, receipts, record, and scripts are individually bound there; no read-only lane was changed.

Every Python invocation used `python3 -I`, taskset CPUs 0,1, CPU 120 seconds, wall 140 seconds, MALLOC_ARENA_MAX=2, disabled bytecode, lane-local temp/cache directories, a 6 GiB address-space safeguard, and an independent RSS watchdog. One Python process ran at a time. HTTP bodies were written into fresh empty per-request directories and never executed or imported. No git, child agents, ledger edits, public messages, uploads, browser tabs, or external build directories were used. The network fetch finished before mathematical computation; no background job is left. The mathematical replay completed with exit status 0.

This is an exclusion recommendation for this campaign's credit standard, **not** a mathematical disproof of the counterexample. Root can retain it as an uncredited observation.

Replay maintenance note: two retained `replay-watchdog-race*.log` attempts stopped when a completed process disappeared between the watchdog's existence check and its `/proc` read. The wrapper now tolerates that normal exit race; the final `logs/replay.log` includes the complete input recheck and JSON validation PASS. These attempts did not reveal a mathematical failure.
