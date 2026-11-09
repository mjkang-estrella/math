# Independent adversarial review: MathDB 356266

**Recommendation: HOLD.** The mathematical counterexample and the extracted Lean certificate are sound under the stated dependency trust. The submitted packet does **not** meet Gate E's explicitly required literal endpoint. There is also material omitted prior art: Albert–West (2009) prints a nonrealizable Euler tour for a restricted permutation class, using precisely strict-comparison-cycle inconsistency. This is not itself a refutation for all of S4, but must be included in the significance assessment before acceptance. No credit or acceptance is granted by this review.

| Gate | Verdict | Reason |
|---|---|---|
| A | QUALIFIED_PASS | The 2022 statement and MathDB match; 1992 corroborates it. Original thesis body unavailable. |
| B | PASS | Independent verification, full S2/S3 enumeration, and 50,000 S4 trials. |
| C | QUALIFIED_PASS | No prior full-Sn refutation located in bounded searches; important restricted-class obstruction recovered; specific coverage limits below. |
| D | QUALIFIED_PASS | A substantive full-S4 counterexample, provisionally; printed-obstruction reuse requires explicit reconciliation. |
| E | FAIL | Fresh strict replay passes, but the endpoint is existential, with no all-n conjecture Prop or theorem negating it. |

## A. Statement and quantifiers

Authors are **Rachel Kirsch, Clare Sibley, and Elizabeth Sprangel**, *Graph Universal Cycles: Compression and Connections to Universal Cycles*, arXiv:2209.14198. The live abstract's submission history lists only v1, 28 September 2022. Its citation metadata identifies the 2023 journal publication, DOI 10.1016/j.aam.2023.102522. I freshly retrieved that sole arXiv version, rather than inferring version coverage from the discovery notes. See downloads/source-abs/body-0 and its receipt; downloads/source-v1/body-0 and text.txt. Text line numbers below refer to this fresh extraction (they agree with the discovery extraction).

The following requested source excerpts are from the supplied manuscript text, independently checked against the freshly downloaded v1:

> Definition 6.1. An ordered pair of permutations (σ, τ) ∈ S_n² overlaps by s if σ_{n−s+1} ··· σ_n ≅ τ_1 ··· τ_s. An ordered pair of permutations (σ, τ) overlaps if it overlaps by n − 1.

> Definition 6.2. The clustered graph of s-overlapping n-permutations, denoted by O(n, s), is a directed multigraph on vertex set S_s. For each π ∈ S_n, there is a directed edge (red(π_1 ··· π_s), red(π_{n−s+1} ··· π_n)). Thus we identify the edge set with S_n. The clustered graph of overlapping n-permutations, denoted by O(n), is O(n, n − 1), the graph of (n − 1)-overlapping n-permutations.

These are lines 789–795, page 15. The surrounding text, lines 776–785, defines S_n(A) using distinct elements of a totally ordered set, order-isomorphism by agreement of **all** strict comparisons, and universal cycles by exactly one window for each permutation. It gives 124324 as an S3 example and notes existence over n + 1 symbols. Lines 796–800 explain the map from a universal cycle to an Euler tour, then state that the converse conjecture remains open.

> Conjecture 6.3 (Conjecture 3.1.3 in [15], [8]). Given any Euler tour of the clustered graph of overlapping permutations (i.e., an ordering of S_n such that each consecutive pair of permutations overlaps), there is a universal cycle for permutations that covers S_n in the same order.

This is lines 801–803, page 15. It is universally quantified in n in context, not a claim for a selected construction or selected n. The cyclic last/first adjacency is part of “Euler tour.” Labels distinguish parallel edges.

> Remark 6.4. It is known [8,18] that given any Euler tour (or Euler trail) of the clustered graph of overlapping permutations, there is a universal word for permutations that covers S_n in the same order. The difficulty in the conjecture is in closing the cycle. In other words, it is not known whether the first and last n − 1 symbols of a universal word for n-permutations can always be made to be identical, or if they sometimes must take on different, order-isomorphic forms.

This is lines 828–832, page 16. Lines 834–837 explicitly discuss the possibility of a graph universal cycle whose permutation order has no ordinary universal-cycle realization. Graph universal cycles do not settle the conjecture in the positive direction.

The alphabet size is unrestricted. Repeated symbols at distant positions are allowed (indeed the examples repeat symbols); within each n-window all symbols must be distinct. Permitting ties cannot rescue a strict comparison cycle. Any finite cyclic word over any linear order uses a finite alphabet, and its used symbols can be ranked as integers. Thus the strong nonrealizability statement over all LinearOrder types covers the numerical/finite-alphabet source meaning. “Same order” permits choice of starting point; rotating a realizing word would realize the fixed displayed start, so the certificate loses no generality.

The supplied raw/356266.jsonl states exactly the arbitrary-tour lifting question. Its “first_stated_year: 2022” is historical metadata, not the actual origin, and is not used for novelty. CDG 1992, supplied sources/chung-1992.txt lines 218–363 (full Section 4), defines length n! words on {1,...,N}, with N free (225–229). Lines 342–346 say the lifted relation is acyclic for a restricted construction and express belief that this holds for any Eulerian circuit. This is the same stronger ordering question. Their separate conjecture that n + 1 symbols suffice for *some* tour is the one Johnson solved in 2009. The restrictions in the earlier **existence proof** do not restrict Conjecture 6.3's “any.”

Hurlbert's thesis, *Universal cycles: on beyond De Bruijn*, Rutgers 1990, Conjecture 3.1.3, was not recovered. His live publication list lists it without a download link (downloads/hurlbert-pubs/body-0, lines 154–166). Searches recovered bibliographic references rather than the body. I cannot quote or certify its original qualifications. This qualifies A; it does not undermine fidelity to the explicitly supplied 2022 target.

## B. Independent mathematics

I wrote scripts/mathematics.py without importing or executing discovery scripts. Run it with scripts/capped.sh python3 -I -B followed by its absolute path. mathematics.json and logs/mathematics.log contain the results.

The 24 displayed rows are exactly S4, without repetition. Ranking each suffix of length 3 equals ranking the next prefix, including last/first. The independent graph includes every strict comparison from every window, on positions modulo 24. It contains

    2 → 5 → 8 → 10 → 13 → 15 → 18 → 20 → 23 → 2.

Windows 2, 5, 8, 10, 13, 15, 18, 20, 23 supply these inequalities, respectively; the independent output also records other windows supplying the same edges. Transitivity yields x2 < x2 in any linear order. Every claimed row comparison is strict, so using larger alphabets or repeating distant values cannot help.

Conversely, for these finite instances an acyclic comparison digraph admits a topological ordering; assigning its distinct ranks to word positions satisfies every required pairwise comparison. Thus the graph test is a complete realization test, not merely a sufficient failure heuristic.

Exhaustive depth-first enumeration, fixing the increasing permutation first to quotient cyclic rotation, gives S2: 1 tour, 0 failures; S3: 8 tours, 0 failures. S1 is trivial. Hence 4 is the smallest positive n with failure, in the unrestricted-alphabet interpretation. Independently seeded shuffled-adjacency Hierholzer search on S4 gives **7 failures in 50,000 trials** (seed 20261105). This is extensive, not exhaustive, and is **not a uniform sample of Euler tours**. It shows rarity under that generator, not a proven proportion of all tours. Three independently found examples are retained. The witness proof does not rely on sampling statistics.

## C. Prior art and coverage

No public full-Sn refutation was found, but this is bounded clearance. The following is an evidence inventory, not a claim that all citing papers were read.

1. **CDG 1992:** full Section 4 read, as detailed above. The printed S4 example is realizable; their text explicitly entertains arbitrary-circuit acyclicity. The live Ron Graham paper list has no adjacent erratum for this item. Web searches for errata located none; this cannot certify absence of an unindexed correction.
2. **Hurlbert–Isaak 1996:** full supplied text inspected, especially lines 225–230. Its warning concerns returning to compatible representatives. It constructs difference-equivalence cycles, and does not print an order-isomorphic nonliftable full-Sn tour. The warning alone is not a refutation.
3. **Hurlbert's later work:** live publication list and the freshly retrieved Jackson–Stevens–Hurlbert 2009 problem collection screened. The latter's relevant discussion (downloads/research-problems/text.txt, 130–192) concerns k-permutations, shorthand representations and weak orders. I found no ordering-conjecture resolution. Thesis body remains unavailable.
4. **Jackson 1993:** OpenAlex locates only the ScienceDirect full-text route, which was not requested because it is denied. The full paper remains unread. Its k-permutation theorem is corroborated by the read Horan and shorthand papers; that is not a full-body novelty clearance.
5. **J. Robert Johnson 2009:** fresh arXiv:0710.5611 full text inspected, especially 50–128. Theorem 1 constructs *some* cycle on n + 1 symbols; it does not lift every reduced Euler ordering. Johnson's S4 example agrees, up to translation, with CDG's printed positive word. Do not confuse J. Robert Johnson with Tobias Johnson of the multisets paper.
6. **Ruskey–Williams / Holroyd–Ruskey–Williams:** fresh conference and journal PDFs and Williams's talk slides inspected for representation and lifting discussion. Journal introduction lines 55–88 defines shorthand windows of length n − 1. The slides distinguish relative-order encoding (roughly 417–439). These results do not resolve arbitrary order-isomorphic lifting. The additional arXiv:0710.1842 manuscript was fetched and its representation discussion screened.
7. **Horan–Hurlbert:** fresh arXiv:1301.1270, especially lines 35–39, 67–87. It uses exact-word s-overlaps with s ≤ n − 2 in the relevant statements, not the disputed reduced (n − 1)-overlap lifting.
8. **Gabric–Sawada–Williams–Wong:** fresh author manuscript inspected; Section V, lines 578–597, defines the shorthand representation and constructs a successor. Its permutation result is not the reduced-order lifting assertion.
9. **Kitaev–Potapov–Vajnovszki:** supplied v1/v2 sources inspected, particularly v2 lines 69–96 and the shortening statements. The text recognizes the closing problem but prints no full-S4 obstruction. Its equal-as-incomparable compressed semantics is different from ordinary repeated alphabet symbols.
10. **Kirsch–Lidický–Sibley–Sprangel:** supplied arXiv:2204.02910 versions inspected; v2 lines 148–164 explicitly retain the all-tour conjecture and illustrate why one bad choice of endpoint labels is insufficient. Their universal word 14625415 failing to close does not prove its Euler ordering has no other realization. Their proof selects a special gluing path. The source/example inventory was read, with independent comparisons below.
11. **Fillmore et al. 2026:** the live author page identifies arXiv:2310.13067; its current PDF was retrieved. The subject is universal partial cycles for ordinary words over finite alphabets, including De Bruijn lifting (lines 572–656), not arbitrary reduced-permutation tours. No target refutation found. The discovery lane's publisher-page evidence was also available, but I do not claim a separate publisher-version comparison.
12. **Other citing sources:** all 163 currently returned OpenAlex CDG citing-work titles are retained in citation-title-screen.txt; this is a title screen. The exact 2023 source has two OpenAlex citers, the shortened-cycle companion and *Universal partial tori*. Both were inspected; the latter discusses word arrays, not this conjecture. Additional retrieved bodies include *Enumerating cycles in the graph of overlapping permutations* (arXiv:1609.02210), *The feasible region for consecutive patterns of permutations is a cycle polytope* (arXiv:1910.02233, 279–296), and Mütze's updated Gray-code survey. Noncyclic word realization in these papers is not cyclic lifting. Several 2025/2026 k-permutation construction/enumeration titles were screened only, not fully read.

**Material additional prior art:** Michael Albert and Julian West, *Universal cycles for permutation classes*, DMTCS proc. AK (FPSAC 2009), 39–50, DOI 10.46298/dmtcs.2727. Fresh primary PDF: downloads/permutation-classes/body-1, after an ordinary 301 redirect; see immutable receipt and text.txt. Lines 98–107 print

    1234, 2341, 3412, 4231, 3421, 4321, 4312, 4123

as a nonrealizable Euler tour of Av4(132,213). Its second, fifth and seventh windows force c2 > c5 > c8 > c2 (their 1-based indices). They also explicitly state the comparison-DAG realization criterion. This is **not** a full-S4 Euler tour: it has only 8 edges. Consequently it does not directly settle the target. Nevertheless the obstruction mechanism and a concrete S4 restricted-class obstruction were published in 2009. Any novelty discussion saying no printed obstruction was found must now be narrowed/corrected.

I tested one natural augmentation independently: form the residual balanced 16-edge graph and insert one Euler excursion into this printed 8-edge tour. In 20,000 seeded trials, every valid full tour so obtained was realizable. scripts/albert_west.py and albert-west-augmentation.json document the negative result. This does not prove that a short multi-excursion augmentation, or another printed restricted-class example, cannot yield the candidate. It prevents claiming that I have demonstrated a routine extension or exclusion. This is the central remaining significance comparison.

Public registries: live Lean Pool HEAD is 01db1d7049cf9668bda1e9e106875ee1278b43e6 (7 October 2026). Its complete recursive tree (25,038 paths, truncated=false), candidates paths, and pinned LeanPool/projects.yml were screened. No Hurlbert/ucycle/universal-cycle match was found. This is metadata/path screening, not every Lean declaration read. Two spaced unauthenticated GitHub repository queries returned 0 repositories for Hurlbert + universal cycles, and one k-permutation generator for the general topic. This does not clear global code search. Live OEIS search returned shorthand-cycle counts, including A120061; its semantics does not concern arbitrary reduced Euler orders. No result was located by the saved broad and exact-phrase web queries (logs/search2.json through search6.json).

Access limits: OpenAlex anonymous text search returned 503; DOI lookups and citing-work filters succeeded. The first guessed CDG DOI was wrong and returned 404; the corrected DOI resolved. These failures are retained, not treated as negative evidence. Crossref, Semantic Scholar, arXiv search API, ScienceDirect and DBLP were never directly requested. Search-engine results incidentally include their snippets; no substantive conclusion depends on their text. No 403/429 or challenge was retried, TLS verification remained enabled, and no account, message, browser or publication action occurred. HTTP requests have fresh per-request directories, every redirect body and response headers, timestamp and SHA256 in downloads/*/receipt.json. Searches do not establish worldwide priority or exclude folklore.

## D. Significance and exclusions

The result refutes the unrestricted all-tour claim, rather than alphabet optimality, existence of some universal cycle, or a compressed/graph variant. The 1992 belief and its explicit preservation as a 2022 conjecture give it standing. The n = 4 witness and short proof are not reasons to dismiss it by themselves.

My independent scripts/printed.py compares cyclic successor pairs with the CDG positive S4 tour and all 64 twin-order expansions of Figure 17. It allows alphabet complement and word reversal (reversing both rows and offsets), with rotation implicit. Maximum agreement is 9/24 and 10/24 respectively, so the witness is not a two-switch reordering of either family. This is limited evidence, not a universal small-modification test. It does not address all Albert–West obstructions.

I find no basis for immediate EXCLUDE from a known full-Sn refutation. I also do not clear a categorical “no reuse of a printed obstruction” claim. Before acceptance packaging, explicitly compare the new full-S4 witness with Albert–West's restricted-class examples and explain the substantive step beyond them. Root should apply the campaign precedent on short augmentations to that comparison. Provisionally D is QUALIFIED_PASS; the prior-art omission needs correction in any final paper/dossier.

## E. Fresh Lean replay and literal endpoint

I safely extracted proof-packet-v2.zip into fresh lane-local replay/ using my own scripts/extract.py. Only the three expected small .lean files were accepted; no archived executable was run. I inspected their contents, then used scripts/replay.sh, under scripts/capped.sh, to run:

    lean -j1 -M3500 -DwarningAsError=true -o Hurlbert.olean Hurlbert.lean
    lean -j1 -M3500 -DwarningAsError=true Inventory.lean
    lean -j1 -M3500 -DwarningAsError=true AllAxioms.lean
    leanchecker Hurlbert

All four returned 0. Logs: build.log, inventory.log, axioms.log, leanchecker.log. The checker log is empty on success. The audit enumerates all 13 namespace declarations, including generated proofs, rejects unsafe/partial/local axioms, and prints their transitive axioms. Only propext, Classical.choice and Quot.sound occur. In particular tour_not_realizable uses only propext. No sorry/admit/native_decide was found in the proof. Lean is 4.34.1, using the supplied read-only mathlib package oleans pinned to d13f23b723b8a846827a245b89c10fc7d3f11612. This trusts those prebuilt imports; it is not an upstream source rebuild or a separate proof-assistant implementation.

Semantic definitions are general: Hurlbert.lean lines 7–25 define finite permutations by injectivity, overlap by all suffix/prefix comparisons, complete cyclic Euler orderings, cyclic position, and realization by all window comparisons. Injectivity of Fin n → Fin n is equivalent to bijectivity; the Euler predicate explicitly asserts both distinctness and coverage, so it cannot certify an incomplete subgraph. Completeness forces the correct factorial tour length. The arbitrary LinearOrder nonrealizability proof at 36–48 is valid and stronger than needed.

But lines 52–54 end with:

    ∃ t : Fin 24 → Fin 4 → Fin 4,
      EulerOrdering t ∧
      ∀ (A : Type) [LinearOrder A] (w : Fin 24 → A), ¬ Realizes t w

This is an existential counterexample certificate, **not a theorem of the form ¬ HurlbertOrderingConjecture**. No Prop states the conjecture for all n in this packet. Its comment “Literal counterexample” and CANDIDATE's “literal Lean certificate complete” overstate compliance with this review's explicit Gate E.

The missing bridge is small, not a mathematical gap in the refutation. One suitable conjecture Prop, using the existing definitions, universally quantifies n, N, and t : Fin (N+1) → Fin (n+1) → Fin (n+1), assumes EulerOrdering t, and concludes ∃ k, ∃ w : Fin (N+1) → Fin (k+1), Realizes t w. A theorem negating it specializes n = 3, N = 23, t = tour, obtains k, w, hw from the conjecture and tour_euler, and applies tour_not_realizable w hw. This directly uses finite ordered alphabets; there is no universe-existential complication. Estimate: roughly 6–15 lines plus rerun of all audits and archive regeneration, not a new combinatorial development. This suggested bridge is not present or independently compiled in the submitted packet. Gate E remains FAIL until the actual revised packet is replayed.

## Provenance, constraints and exact next evidence

All writes, TMPDIR, caches, downloads and builds stayed inside hurlbert-review-r1. There were no agents, git calls, source-lane edits, shared-ledger edits or background jobs left running. Python commands used python3 -I -B and absolute script paths. scripts/capped.sh restricts affinity to 2 allowed CPUs, CPU time to 120 s, wall time to 140 s, MALLOC_ARENA_MAX=2, and watches the process group for a 6 GiB aggregate RSS ceiling. All Lean calls additionally have -M3500. Heavy runs were sequential.

inputs-before.sha256 and inputs-after.sha256 are identical manifests for 302 input files; logs/hash-check.log reports all OK. They bind the discovery source/notes/scripts/replay inputs, candidate, packet and MathDB record. Principal hashes:

- CANDIDATE.md: 8ea3185bad721703bc37261d2fbff513c062ea60e9a36dacaadc4fa7c8494082.
- proof-packet-v2.zip: d81d64bccc8dfcccddba997238d50718dc0d25de02897eb4c6fc0b0f1e0b92e2.
- raw/356266.jsonl: 933e1d9bff9c87571d9caff4ca029e4573e4af3b689cda453c675249245b753d.

To lift HOLD: (1) produce and freshly replay a packet with the all-n conjecture Prop and literal negation, auditing the new declarations; (2) correct and substantively reconcile the Albert–West printed obstruction under the campaign's augmentation exclusion rule. Original thesis and Jackson full-body recovery would strengthen historical clearance, but their unavailability must remain candid if no allowed route is available. Root alone decides acceptance.
