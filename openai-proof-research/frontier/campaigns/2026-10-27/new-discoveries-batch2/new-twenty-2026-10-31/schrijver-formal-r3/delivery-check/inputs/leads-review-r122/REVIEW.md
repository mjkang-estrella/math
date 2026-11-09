# Independent review of r122 leads

Reviewer recommendation: **HOLD for 352905; HOLD for 352827.** Neither is accepted, and accepted credit remains zero. Root decides. Both ordinary counterexample calculations survive. Neither journal body was cleared through the bounded open routes. There is a stronger Schrijver lead at **k = 12, r = 3**, independent of the erroneous r = 2 theorem.

## 352905: spider e-positivity

The exact target is Wang and Wang, [arXiv:2112.06619v1](https://arxiv.org/abs/2112.06619v1), Conjecture 3.5, with a ≥ b ≥ 2, b even, and b not 2 modulo 3. Leg parameters are edge lengths. Thus b = 24 gives S(600,24,1) on 626 vertices and satisfies every hypothesis.

### Independent derivation and exact recomputation

Start directly from proper colorings. Inclusion-exclusion over edges gives

    X_G = sum_{F subset E(G)} (-1)^|F| product_{C component of (V,F)} p_|C|.

For a path, edge subsets correspond bijectively to compositions of its vertex count into consecutive component sizes. Set Q(z) = sum_{j≥1} (-1)^(j-1) p_j z^j. Consequently F(z) = sum X_Pn z^n = 1/(1-Q(z)). From E(z) = product_i (1+x_i z), formal logarithmic differentiation gives Q = z E'/E. Therefore

    F = E/(E-z E') = E/(1 - sum_{j≥1} (j-1)e_j z^j).

This derivation uses neither r122 script nor a conjectural formula.

Here is an independent proof of the needed spider identity. Separate edge subsets according to whether the pendant edge is absent or present. The absent contribution is p_1 X_P(a+b+1). For the present contribution, let x and y count selected consecutive edges from the center into the a and b legs before the first cut, with 0 ≤ x ≤ a and 0 ≤ y ≤ b. Its central component has x+y+2 vertices and sign (-1)^(x+y+1); the remaining factors are X_P(a-x) X_P(b-y). Exactly the same terms occur among the edge subsets of P_(a+b+2) containing its bridge between consecutive blocks of a+1 and b+1 vertices. The subsets missing that bridge contribute X_P(a+1) X_P(b+1). Hence

    X_S(a,b,1) = e_1 X_P(a+b+1) + X_P(a+b+2) - X_P(a+1) X_P(b+1).

Set e_5 = x, e_6 = y, and all other positive-degree e-generators to zero. Algebraic independence of the elementary basis makes this a valid coefficient extraction. The path series is (1+xz^5+yz^6)/(1-4xz^5-5yz^6). The independently implemented recurrence is

    C(t,u) = 4 C(t-1,u) + 5 C(t,u-1)
             + 1_{(t,u) in {(0,0),(1,0),(0,1)}}.

Negative indices have coefficient zero. Exact integer arithmetic gives

    C(124,1) = 781 * 4^124,
    C(5,0) = 5 * 4^4,
    C(119,1) = 2999 * 4^118.

The unique subpartition of (6,5^124) of weight 25 is (5^5). The e_1 term cannot contribute. Thus the spider coefficient equals

    781 * 4^124 - (5 * 4^4)(2999 * 4^118)
      = -2499 * 4^122 < 0.

This is a correct ordinary refutation of the arXiv conjecture.

`scripts/spider_review.py` additionally enumerates proper colorings up to relabeling using restricted-growth strings. For type λ it multiplies by the factorials of multiplicities of equal color-class sizes, obtaining the actual monomial-symmetric coefficient. It independently constructs the elementary-to-monomial change-of-basis matrix by choosing distinct colors within each elementary factor and solves it over exact rational numbers. Every one of the **11 unordered three-positive-leg spiders on at most 8 vertices**, including c > 1, agrees with the path/spider formula in every elementary coefficient. This checks full symmetric functions, rather than just a target coefficient or chromatic polynomial. Full expansions are in `outputs/spider-review.json`. No assertion about spiders with four or more legs is intended.

### Prior art and significance

The 2023 journal article is *The e-positivity and Schur positivity of some spiders and broom trees*, DAM 325, 226–240, DOI 10.1016/j.dam.2022.10.012. OpenAlex reports its journal record closed and supplies no repository copy. The accessible arXiv page still lists only v1. Searches for an author/open journal copy did not produce its relevant body. I therefore cannot certify that the journal retains, restricts, or omits Conjecture 3.5.

Primary bodies and relevant passages checked include Zheng [2008.05038](https://arxiv.org/abs/2008.05038), Tang–Wang–Wang [2405.04915v4](https://arxiv.org/abs/2405.04915v4), Wang–Zhou [2401.01027](https://arxiv.org/abs/2401.01027), [2405.11946](https://arxiv.org/abs/2405.11946), *Clocks are e-positive* [2410.07581](https://arxiv.org/abs/2410.07581), Tom's [FPSAC 2025 paper](https://www.mat.univie.ac.at/~slc/wpapers/FPSAC2025/118.pdf), Li [2503.09484v2](https://arxiv.org/abs/2503.09484v2), and Wang–Wang [2608.22184v1](https://arxiv.org/abs/2608.22184v1). These were targeted statement/proof checks, not full audits of every theorem. Tang et al.'s positive family has a = 2b+2, not a = b²+b. Tom's finite classification conjecture requires c ≥ 2. The 2026 clique-spider classifications concern different graphs; that paper explicitly says no comparable classification is known for shortest leg 1. Li's general coefficient formula can recompute this answer, but is not itself a stated refutation; its displayed local obstructions do not immediately apply to this spider, which has pendant P_4 subtrees. No exact composite-(b+1) non-e-positivity statement was identified in the checked passages.

The live Wang author listing also exposes October 2026 papers [2610.03464](https://arxiv.org/abs/2610.03464) and [2610.39481](https://arxiv.org/abs/2610.39481). Their primary abstracts concern Schur positivity and the degree-four caterpillar obstruction, respectively; neither abstract resolves this degree-three e-positivity target. Their bodies were not cleared, a remaining limitation. Search coverage included the requested author names; no claim of complete author bibliographies is made.

OpenAlex's journal citing-works query returned four works, all recorded in `sources/spider-citing.json`. Three open mathematical bodies were checked above; the fourth concerns local vertex energy in double brooms. Citation indexing is incomplete: it misses several relevant arXiv papers. Empty exact searches are not novelty evidence.

**Significance judgment:** this is potentially a genuine conjecture refutation, not a substitution into an already-proved non-e-positivity theorem. It requires choosing a new coefficient support using a factorization of b+1. However, the coefficient extraction is elementary and follows exactly the source's working method; there is no new CSF identity. Under the campaign's strict prohibition on routine source-formula bridges, root must explicitly adjudicate that objection. I do not recommend exclusion solely because the final calculation is short, nor recommend a large formalization yet. The composite mechanism first becomes available at admissible b = 24: preceding admissible b ≥ 2 are 4, 6, 10, 12, 16, 18, 22, whose b+1 are prime. This does **not** prove e-positivity for those earlier cases or global minimality of b = 24.

Recommendation: **HOLD**, pending journal-body comparison, the latest relevant paper bodies, and root's substantive-significance decision. The large symmetric-function semantic Lean bridge is still absent.

## 352827: Schrijver diameters

The source's vertices are cyclically 2-stable k-subsets of [n], adjacent precisely when disjoint. No definitional difference explains the discrepancies. v1 has neither the added r = 2 Section 3 nor Theorem 6/Conjecture 2; these occur in v2. The v2 proof of Theorem 6, including its preceding layer description, was read.

### Independent computation and certificates

The new program recursively lists increasing subsets with gaps at least two and removes the cyclic-endpoint violation. It checks the exact vertex count n/(n-k) * binomial(n-k,k). Adjacency is formed by unions of coordinate-incidence bitsets and complementation. Breadth-first distance layers are computed from every rotation-orbit representative. Rotations preserve both stability and disjointness, so this covers all source vertices; no dihedral assumption or source code is used. A separate checker recomputes every certificate edge from literal disjointness, checks stable-set completeness by the count, checks the BFS-layer equalities, and checks rotation coverage. All seven retained certificates pass.

| (n,k) | Vertices | Exact diameter |
|---|---:|---:|
| (14,6) | 49 | 5 |
| (15,6) | 140 | 4 |
| (16,7) | 64 | 6 |
| (17,7) | 204 | 5 |
| (18,8) | 81 | 6 |
| (19,8) | 285 | 6 |
| (22,10) | 121 | 8 |
| (23,10) | 506 | 6 |
| (27,12) | 819 | 8 |
| (28,12) | 3185 | 6 |
| (29,13) | 1015 | 9 |
| (30,13) | 4200 | 7 |

The finite Table 1 ranges were recomputed for k = 2 through 6, including the first n in its diameter-2 tail. For k = 7, n = 15 through 24 completed; n = 25 hit the wall cap, first in a cumulative run and then in an isolated instance. No result for that instance is asserted. n = 26 exceeds the chosen 60,000-vertex enumeration cap. The infinite tails are not finite enumerations. For n ≥ 4k-2 an elementary check proves diameter 2: any intersecting distinct pair leaves at least 2k-1 positions in its complement, a union of paths on the cycle, which has an independent k-subset. The graph is not complete. This explains the tail but is not claimed as fresh computational coverage. Full additional coverage for k = 8 through 16, and every skip, is in the graph logs. No universal minimality claim is made.

For an explicit distance-5 pair in SG(14,6), take

    A = {1,3,5,7,9,12}, B = {1,3,6,8,10,12}.

A path of length 5 is

    A,
    {2,4,6,8,10,14},
    {1,5,7,9,11,13},
    {3,6,8,10,12,14},
    {2,4,7,9,11,13},
    B.

All sets are cyclically stable and consecutive sets are disjoint. For the lower bound, enumerate the two closed radius-2 balls using all 49 literal vertices. Their sizes are 17 and 13 and their intersection is empty. The full lists appear in `outputs/certificate-checks.json`; the independently checked literal adjacency and layers appear in `outputs/graph-14-6-certificate.json`. If a path of length at most 4 existed, its middle vertex would belong to both balls. Thus dist(A,B) = 5. This is a finite exhaustive ordinary certificate, not a Lean theorem.

### Error in Theorem 6 and a route independent of it

On v2 page 19 the proof claims that j-i = k-floor(3k/4)-1 makes k+i+1-j at most floor(3k/4). Substitution gives **floor(3k/4)+2**. The subsequent “without loss” restriction on j-i consequently does not exhaust the needed cases. Even the later bottom-layer maximal-distance discussion does not repair that arithmetic. This identifies a concrete invalid step; I do not claim it is the proof's only error. Its displayed upper bound cannot establish the theorem, and the pair above disproves the printed value 4 for k = 6. Table 1 repeats that error. The claimed k = 10 diameter 7 similarly conflicts with the computed 8.

Under the brief's rule, the original k = 10, r = 2 example should be classified as a **source-internal correction with zero credit**: retaining the source's printed 7 would give 7-6 = 1. That route alone does not justify Lean investment.

However the independent check found

    D(SG(27,12)) - D(SG(28,12)) = 8 - 6 = 2,
    D(SG(29,13)) - D(SG(30,13)) = 9 - 7 = 2.

Both have r = 3 and satisfy 2 ≤ r ≤ k-2. Neither uses Theorem 6, and neither graph is an r = 2 graph. They therefore refute the literal v2 Conjecture 2 independently of its erroneous formula. For the first pair of graphs, the 819-vertex certificate supplies distance 8 for the explicit pair in `logs/cert-k12-r3.log`, while the 3185-vertex certificate supplies an upper bound 6 for every pair; that is already sufficient to force a drop of at least 2. Exact equality is checked too. This is a stronger candidate than the originally proposed source correction. No theorem in the source's stated r ≥ 3 bounds is contradicted by these values.

### Later literature and recommendation

The journal article is DAM 350 (2024), 15–30, DOI 10.1016/j.dam.2024.02.019. OpenAlex points only to the arXiv submitted version as its green copy. The live arXiv abstract still lists v2 as latest. Open searches identified no open journal body, correction, or later exact diameter result resolving these examples. The one OpenAlex citing journal work concerns strong diameters of graph products, not Schrijver graphs. The independent recommendation is **HOLD**, not EXCLUDE: r = 3 survives the source-conflict objection, but the current journal scope and bounded novelty clearance remain incomplete. If those gates clear, prefer the k = 12, r = 3 certificate route over the k = 10 correction route for formalization.

## Provenance, limitations, and operations

All 289 r122 files were SHA-256 hashed before reading the copied inputs. They remain read-only. `inputs-before.json`, `inputs-after.json`, and `outputs/input-integrity.json` supply the before/after binding. Local copies are in `inputs/`; own programs are in `scripts/`. No r122 script was executed, imported, or reused. HTTP bodies and dated status/hash receipts are in `sources/`; full computation stdout/stderr is in `logs/`. The initial search tool response was displayed in the session but not captured as a standalone file; subsequent searches are retained in `outputs/search-2.json` through `search-5.json`.

ScienceDirect, Crossref, Semantic Scholar, and the arXiv search API were never requested. Search-engine snippets sometimes included ScienceDirect URLs; these were not opened or treated as body clearance. An arXiv monthly-list request returned 400 and was not retried. One mistaken Omega organization URL returned 404; the correct organization was then read from the cached receipt. No forbidden denied route was retried. The bounded search used approximately 40 discovery/HTTP requests for the spider and substantially fewer for Schrijver, with shared registry checks; redirects and search-engine backend subrequests are not independently countable.

OpenAI/math's live HEAD is unchanged at 4eaee87548250b2682affda7d05d947c05554bae. Omega's correct live HEAD advanced to b715a9e2e5f439f86a18f5ed9511efbe75c6061d; its head commit concerns a Bajnok–Beatty result. This alone cannot clear intervening commits. The recursive tree fetch succeeded but reports **truncated = true** with 56,432 entries. Its bounded path screen is retained in `outputs/current-registry-path-screen.json`; no complete registry clearance follows. A current complete proof-body registry audit is **not** claimed; this is another reason not to release a novelty hold.

Final integrity check: all 289 original files are unchanged. Both before and after hash-list files have SHA-256 `a47db162e2851363f2750a04bee063f4bc2faed8942e0c7f2b6a8a5756c3cd79`. Seventy-five distinct graph instances completed, as listed in `outputs/graph-combined.json`. There are seven independently checked retained graph certificates.

The computational launcher fixes CPUs 0 and 1, CPU time 120 seconds, address space 6 GiB (stronger than an RSS ceiling for these processes), wall time 140 seconds with a two-second kill fallback, MALLOC_ARENA_MAX=2, lane-local TMPDIR and caches, and python3 -I. No packages were installed. There are operational exceptions: the initial brief/AGENTS/inventory read-only shell commands preceded this wrapper; and the short k = 8 through 16 batch began before the yielded k = 6 run had been collected, causing a brief overlap of numerical processes. This violated the one-heavy-process sequencing instruction; later certificate runs were serialized. These exceptions are disclosed rather than claiming perfect procedural compliance. Both large k = 7 timeouts are preserved and were not interpreted as mathematical results.

No child agents, Lean, git, external messages, uploads, browser tabs, shared ledger edits, or self-acceptance occurred. Root must adjudicate the findings and procedural exceptions. No running job is intentionally left at handback.
