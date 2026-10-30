# Independent preliminary adversarial review: diamond–path edge-irregulator family

Review date: 2026-10-29 UTC. Reviewer: Sol, high reasoning, solo. Candidate: `sol-fresh-source-discovery-r70`, frozen at 17:11:27.311789 UTC by `root-edge-irregulator-review-freeze-r1/review-freeze.json`. This review is an independent assessment, not acceptance or a formal-certificate review.

**Recommendation: HOLD.** The ordinary refutation is correct. The specified older theorem bodies do not give a complete prior bridge to this family or an asymptotic deletion fraction greater than 1/3. The construction addresses the full intended source question, rather than a normalization defect or a fixed guessed constant. However, current public-registry completeness/head verification remains missing. Do not begin substantial formalization or award discovery credit on the strength of this review. Candidate credit remains **0**; campaign counts remain **7 additional / 37 total**.

| Gate | Finding |
|---|---|
| SOURCE | PASS for the exact arXiv and author-deposited conference assertion; publisher-certified statement not independently obtained |
| MATH | PASS, complete ordinary infinite-family refutation |
| NOVELTY | HOLD: bounded body comparisons clear, current inventory/head clearance incomplete |
| SUBSTANTIVE | PASS within the investigated bodies: genuine full-question obstruction; no complete routine subsumption bridge identified |
| FORMAL feasibility | Plausible finite-combinatorial endpoint, conditional on eligibility; no Lean certificate or compilation claimed |

## Freeze, scope and method

Read repository and batch AGENTS, ledger, prior-campaign context, candidate PROOF.md, SUMMARY.md, discovery.md, provenance and primary/prior text bodies. Reconciled the accepted and excluded/held families: this family is not another credit for any listed acceptance. Past valid-but-routine exclusions remain relevant to the substantive test; a short proof does not itself establish eligibility or ineligibility.

Before using the copied evidence, `sha256sum -c` verified **79/79** candidate files against the supplied freeze. Each was copied as ordinary bytes into this lane's `frozen/`, with no links to candidate files, and the copy independently verified **79/79**. The freeze JSON hash is `ffccfd453ec2170a54ecc4e37c69678e5af1434c87f707c698f4ab263b7d96b2`. All mathematical inspection and new checks used this copy. Final rechecks of the original candidate and private copy are recorded in `freeze-after.log` and `copy-after.log`; a membership comparison also checks that neither tree gained or lost files. See `freeze-summary.txt` for the final outcome. No git operations, shared edits, children, contacts, browser tabs, posts or external mutations were performed.

New Python helpers were launched exclusively through the byte-identical copied `capped_run.py`: per-process AS 512 MiB; sampled process-group RSS 512 MiB and CPU 210 seconds; wall 230 seconds; 40 ms nominal sampling; BLAS thread variables 1. No cap was raised. Sampling is nominal, not a guarantee against scheduler delay or unsampled transients. The supervisor is the supplied runner, not a newly strengthened resource monitor. Existing candidate failures are preserved, including missing NetworkX and a guessed registry-module 404. My checker and HTTP refresh both exited 0. An initial shell context read failed because the repository working directory was omitted; it was repeated with the explicit directory and made no writes. No experimental failure was discarded.

## SOURCE: exact quantifiers, conference status and chronology

The definition concerns a subset S of **edges**, and degrees are those in G−S. Only retained adjacencies must have unequal endpoint degrees. Isolated vertices are allowed, and the retained graph need not stay connected. The input graph must be connected. There is no minimum-degree, regularity, bipartiteness, high-connectivity, or retained-connectivity premise excluding these graphs.

The literal claim is: there exists one absolute real c≥1 such that for every connected finite simple G, I_e(G)≤|E(G)|/3+c. Both the existential constant and universal graph quantifier matter. I read the exact v1 text around Conjecture 1 and Theorem 2.1, and the HAL conference text around its definition, Conjecture 1 (printed p.4, physical PDF p.5) and Theorem 1. I also inspected the frozen page image: the absolute constant, connected quantifier and fraction 1/3 are legible. This is not an inferred conjecture from an abstract.

[arXiv:2511.14514](https://arxiv.org/abs/2511.14514) lists only v1, submitted 2025-11-18 14:11:47 UTC, as independently refreshed at 17:14:33 UTC. The [HAL author manuscript](https://hal.science/hal-05548898v1/document) cover records submission 12 March 2026 and WALCOM 2026 pp.353–367, DOI [10.1007/978-981-95-7127-7_24](https://doi.org/10.1007/978-981-95-7127-7_24). The [official conference program](https://mozart.diei.unipg.it/walcom2026/Program.pdf), freshly downloaded and text-read, lists the paper and all five authors. The chapter's publisher endpoint in the frozen provenance returned a cookie-error page; I did not obtain a publisher-certified PDF. The proper source description is **an author-deposited conference manuscript containing the conjecture**, supported by conference publication metadata. It is not publisher-text certification.

The DMTCS prior PDF identifies arXiv:2307.04583v7 dated 9 December 2025, revisions 27 December 2024 / 29 October 2025, accepted 27 November 2025. Thus its final v7 date follows the target's November submission but precedes the conference deposit. Its antecedent IPEC work is older. DMGT volume 45 (2025), pp.351–376, is prior labelling work. These distinct chronologies must not be collapsed into a claim that every final PDF predates v1.

Fresh title/refutation/correction searches and the two authors' publication pages located no matching follow-up in the examined results. This is a bounded observation, not proof that no follow-up exists. HAL's landing page returned Anubis access denied during this review; I stopped that route, used the verified frozen document, and did not retry or bypass it. Source assertions here attach to those exact frozen bytes.

## MATH: independent derivation and strongest falsifier

For integer t≥2, use a hub h and six distinct private vertices a_i,b_i,c_i,d_i,x_i,y_i for each block. The eight edges are ab,ac,ad,bc,bd,cx,xy,yh. Distinct blocks share only h. There are 6t+1 vertices and 8t edges; no loops or repeated unordered pairs. Every private vertex connects to c and then to h, so the original graph is connected. Triangles are permitted by the source.

For any deletion set making the retained graph locally irregular, fix a block and let ε be 1 or 0 according as cx is retained or deleted. No other exterior edge changes a diamond degree. If zero diamond edges are deleted, retained ab joins degree 3 to degree 3. With exactly one diamond deletion:

- deleting ab leaves retained ad joining degree 2 to degree 2;
- deleting ad leaves a of degree 2 and b of degree 3; if ε=0, retained ac joins degree 2 to degree 2, and if ε=1, retained bc joins degree 3 to degree 3;
- deleting ac leaves retained ad joining degree 2 to degree 2.

Swapping a and b covers bd and bc. These are final degrees in the whole retained graph, not original degrees. Therefore every block loses at least two diamond edges. Independently, retaining cx,xy,yh together leaves x,y each of degree 2, conflicting at xy. At least one of these three path edges is deleted. These charges are disjoint within and between blocks. Shared h does not make any edge shared, and its unknown final degree never enters this lower bound. Consequently |S|≥3t.

Delete ab,ad,xy in every block. Final degrees (a,b,c,d,x,y) are (1,2,3,1,1,1), with hub degree t. Retained edges ac,bc,bd,cx,yh have degree pairs (1,3),(2,3),(2,1),(3,1),(1,t), all unequal for t≥2. Thus I_e=3t. Any isolated vertices that another deletion set creates impose no extra constraints; this cannot defeat a lower bound quantified over all deletion sets. The displayed upper witness itself has no isolated vertices. The t≥2 restriction is essential to this witness because (1,t) would conflict at t=1; no t=1 equality is claimed.

For any proposed c≥1 choose integer t>3c, using the Archimedean property. Then I_e−m/3=t/3>c. Thus the existential absolute constant is negated; the result is stronger than finitely many violations at c=1. No source upper bound or numerical approximation is used as a proof premise.

The strongest local mathematical falsifier is **a block with at most two deletions satisfying all its internal retained-edge constraints, even after dropping the hub-edge constraint entirely**. Dropping a constraint enlarges the admissible set; this is stronger than checking a few convenient hub degrees. My exhaustive 256-mask relaxed test finds minimum cost 3. Separately, all 64 diamond boundary states (32 diamond masks × two ε values) obey the two-deletion lower bound. These finite checks confirm, rather than replace, the cases above. A second falsifier would be a missing source restriction excluding the original graphs; none appears in the inspected versions.

## Own exact evidence and reproduction

`checker.py` was written afresh and imports no candidate checker or graph package. Its private vertices have integer indices and every retained degree is accumulated directly from the literal edge list. Its tests are:

- all 64 diamond boundary states, with every final degree recorded;
- all 256 local retained masks with the hub constraint discarded: 54 admissible masks, minimum 3 deletions, eight minimizing masks;
- every one of 65,536 retained masks of the literal 13-vertex t=2 graph: optimum 6 deletions, **28 minimizers**, all saved;
- t=2,…,200 literal constructions: simple edge counts, connected vertex set, exact final degrees and 3t witness all PASS (199 graphs).

The exhaustive t=2 distribution, by deletion count, is {6:28, 7:120, 8:305, 9:248, 10:485, 11:86, 12:195, 13:6, 14:25, 16:1}. Empty retained graphs and all isolated vertices are handled by the same degree predicate. No dynamic-programming assumption about independent hub states was imported.

Reproduce from this review directory:

```sh
python frozen/capped_run.py python checker.py > checker.log 2> checker-guard.json
```

Original run: UTC 17:13:36, exit 0, no guard reason, sampled peak group RSS 12,857,344 bytes, elapsed 0.2993 seconds. `checker.py` SHA256 `1b74a836c5b0cb0ac6e29caa616b360563468a116b4554a55edc17603451193f`; original `checker-results.json` SHA256 `de2ab17fb644765b1bd464c4388a701ad7ca2d666ef3c72e756654bfbe1d902f`. Reproduction regenerates a UTC field, so a replay's result-file hash will differ while its mathematical fields should match. No large search or formalization was run.

## NOVELTY and SUBSTANTIVE: actual older bridges adjudicated

The closest source lower bound is arXiv Theorem 2.1 / conference Theorem 1: subdivide every base edge twice and charge one deletion per resulting three-edge path. Applied as a local argument to the attachments here, that accounts for only t deletions out of 8t edges. Applying its literal global theorem requires all edges to be subdivided; the diamond edges here are not. A new bridge must prove an attachment-stable diamond penalty and combine disjoint charges. Those steps are established above, and the old theorem alone supplies neither. Its m/3 lower bound also cannot by itself contradict m/3+c.

I read [DMTCS 27:3 #28 (2025), §4](https://dmtcs.episciences.org/17071/pdf), including Theorems 4.1–4.3, their constructions and Claim 1 bodies. The mathematical distinction is not merely that their titles concern complexity:

- Theorem 4.1's Claim 1 forces three deletions from each variable-edge set E_i. Its literal vertices u1,…,u12, two literals, occurrence edges and clause interface are a larger bipartite gadget. It contains neither this diamond nor this eight-edge rooted block. The clause attachment alone adds two leaves and a seven-vertex star per clause. Three deletions per such much larger E_i do not furnish an edge ratio greater than 1/3. The case proof depends on the displayed variable degrees/interfaces, not a general assertion about all rooted graphs.
- Theorem 4.2 builds degree-padding gadgets H_b with equal-degree w,y, large leaf sets and selectable external neighbors. Its Claim 1 under a tight total budget forces one selected edge into the interface. One deletion per large gadget supplies no >1/3 density. The proof does teach a known boundary-forcing method; that general method is not an existing theorem proving the present eight-edge obstruction.
- Theorem 4.3's rooted trees T_i,j enforce forbidden degrees through n² replicated children and high degree padding. Claim 1 is conditional on optimality and the threshold |S|<n²: either S lies wholly in the base graph or has size at least n². It is not an unconditional three-deletion charge in a constant-size block. Its many star edges dilute that threshold; no specialization of the displayed construction gives this family or the required linear excess.

Thus the reviewed gadget bodies neither contain the family nor give a complete existing bridge to >1/3. Replacing their gadgets with these diamonds would require the new stability lemma, not just substitution into their theorem.

I read the proofs of [Bensmail, DMGT 45 (2025), Theorems 9 and 19](https://bibliotekanauki.pl/articles/59945820.pdf). Theorem 9 bounds the count of label-1 edges in proper positive edge labellings, via paths of length divisible by four. Those sums must distinguish endpoints of every original edge. A deletion solution can be written with binary indicators only if zero is permitted and constraints at zero edges are removed; this does not meet the theorem's positive-label/original-adjacency hypotheses. Theorem 19 starts with a **vertex** irregulator and extends labels from its induced remaining graph. Its lower bound on achievable 1-labels cannot be reversed into the required edge-deletion lower bound. Neither body contains a complete bridge.

At the supplied immutable Omega revision, actual `D5/S3/Combinatorics/EdgeLabeling/CycleStarIrregularity.lean` defines vertex labels φ, edge weights φ(u)+φ(v), and injectivity across distinct unordered edges, minimizing the feasible label bound. It is not degree irregularity after edge deletion. Actual `D5/S3/ConceptDynamics/GraphIrregularity/LinkIrregularTournamentExistence.lean` compares directed-link isomorphism types and proves an existence iff n≥6 on n≥2. It is not an undirected deletion assertion. I read those definitions and result statements, without claiming to replay their certificates. `Blueprint/D5` and Lean `D5` are distinct trees; a Blueprint filename hit is not Lean-source coverage.

On this evidence, this is a substantive full-scope refutation: original graphs meet intended hypotheses, and a positive linear gap remains after connectivity costs. Short case analysis and a known charging technique do not constitute an exclusion by themselves. Conversely, I do not certify novelty merely because the source conjecture remained printed. A complete earlier rooted obstruction theorem, exact public counterpart, or an elementary specialization of another prior theorem would reverse this gate. Broader locally irregular decomposition/degree-constrained-subgraph literature has not been exhaustively body-read here; the bounded substantive PASS is not worldwide absence evidence.

## Current-registry check and access limits

Performed fresh public web searches for the title with counterexample/refutation/correction, edge-irregulator with diamond, and relevant registry domains; inspected current accessible repository landing pages for [Omega](https://github.com/the-omega-institute/trureturing) and [OpenAI math](https://github.com/openai/math). Their rendered current views exposed no latest commit SHA. The OpenAI view lists 721 manuscripts / 373 families, versus the pinned local 719 / 372 catalogue: the old catalogue plainly cannot certify current completeness. No new exact counterpart emerged in the examined search results; irrelevant issue/search hits were not treated as mathematical evidence.

I did **not** retry the previously limited GitHub API, rotate credentials, use another API proxy, or claim the earlier 403/429 had reset. Public search and ordinary landing-page reads supplied only bounded current observations, not a replacement complete tree. Omega `6c27b0a84f560fa3e43d128d8a7f9e5f247e0be3` remains the supplied latest-observed 15:49 UTC revision, **not verified current HEAD**. OpenAI `fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb` remains the immutable trusted base, not a current-head assertion. No complete current inventory diff was obtained. This requirement is attempted but **not discharged**; NOVELTY remains HOLD. There is no universal absence, priority, MathDB solution-array, or exhaustive specialist-database claim.

## FORMAL feasibility, only after the preceding assessment

No ordinary mathematical bridge remains conditional. Eligibility is still on HOLD, so I did not launch Lean or build a large development. After clearance, a literal formal endpoint should negate the universal connected finite simple graph bound, using actual retained-subgraph degrees and finite edge cardinalities. A suitable formulation can quantify over finite vertex types (or all `Fin n` graphs), define edge-irregulators as finite subsets of the source edge set, and use the equivalent assertion that some valid deletion set has cardinality ≤m/3+c. The minimum exists because deleting all edges is always valid; this equivalence must be proved if an infimum/minimum definition is used.

The nontrivial implementation obligations are explicit graph construction on `Unit ⊕ (Fin t × Fin 6)`, connectivity paths, exact neighbor sets and degrees, disjoint eight-edge block partitions, the arbitrary-S boundary lemma, cardinal summation, the upper witness and real/natural casts for t>3c. The local cases can be proved propositionally with finite case splitting or kernel `decide`; large-mask computations and `native_decide` are unnecessary. An abstract gadget theorem with an assumed stability property, a predicate named after the conjecture but lacking literal graph semantics, or only a fixed t=2 check would not meet the endpoint. Only propext, Classical.choice and Quot.sound are permitted by the campaign; proof holes, new axioms and unsafe shortcuts are not acceptable. Feasible is not completed: no compile, axiom audit, source-level Lean equivalence, paper or extracted replay is supplied by this review.

## Precise remaining obligations and decision

1. Obtain lawful fresh registry heads and complete relevant inventory/body coverage once access permits, or have root explicitly adjudicate the remaining current-priority limitation. A second stale grep or another short keyword search does not discharge it.
2. Preserve the bounded literature comparison above, and investigate any actual rooted-gadget/general obstruction lead uncovered by that fresh coverage. Exclude discovery credit if it supplies a complete prior bridge; do not count helpers or this exact I_e equality separately.
3. Only after eligibility clearance, implement the literal infinite-family Lean theorem and source-quantifier negation, audit declaration types and axioms, prepare the paper/packet, obtain independent final review and a fresh strict extracted replay.
4. If publisher-certified wording is required by root, obtain it lawfully and compare the exact conjecture. Until then use the accurate author-conference-text description.

**HOLD, not EXCLUDE:** no mathematical defect or complete earlier subsumer was found in the investigated bodies. **HOLD, not INVEST yet:** the required current-head/inventory check is incomplete, and formal feasibility cannot compensate for that. Preserve this independently checked ordinary proof with candidate credit 0.

## Provenance manifest

All 79 frozen source hashes and original acquisition UTC/URLs/statuses are in `review-freeze.json`, `freeze.sha256`, and `frozen/provenance.json` / `frozen/http.jsonl`. Key bytes actually read:

| Evidence | SHA256 |
|---|---|
| PROOF.md | e00d699351e9bc05cad58d2efe93498c397bc6f48ae592a4b837b65fe35db59c |
| arXiv v1 HTML | 268d472c996ddd76731df104c7a0cd6d420afcc727a99a353d685ed11342d24d |
| HAL author PDF | a72070ef2e89ba2e2056e94b94d9a22d0ee788fc3270c0cbe8313f1e66760fbe |
| HAL conjecture page PNG | 10b508cd40d576ac84fd2e7e59cda1ea4cf3b1b29673155bde8b00053dffe802 |
| DMTCS prior PDF | 268ba5f885ef7914184316389dbdaf2c42f6d8a64039384d1e9cf83f4e2b22df |
| DMGT prior PDF | 3b726dfa71bde946bfc130db9a1fa4c045455d001e972d503c6e2c4bae08b886 |
| actual cycle-star Lean | 0d968b30aaae4bdbae84495473f3fb118192ed2e72561e498d1577bbbd71c524 |
| actual tournament Lean | 4b65dc29dffd678f6558634620bb981fede0697476ac270401f2b4919b6319ff |

Fresh HTTP observations in `live/http.json`: arXiv abs at 17:14:33.876456 UTC (200, SHA256 `cdabe33f2b269c74c3bae9d9203e0aedc4612839e0daf0b24cedee8a2e8fe816`); official program at 17:14:33.907714 UTC (200, `61a0308f1fa21c300162830632e67859ef6e3ca2c0439d6ad43f794af9451eb4`); author homepage at 17:14:35.986616 UTC (200, `3fe1e92d7056610c27a94bbd9c8181e8f7d727758f5ccd55addf70ee076f44b4`). Their URLs, redirects and headers are saved. HTTP Last-Modified and cache timestamps are not publication chronology. Refresh guard: exit 0, sampled peak RSS 25,268,224 bytes, 3.0602 seconds.

Fresh search/landing-page records are in `live-web-results.json` and `live-web-details.json`, each timestamped; these archive the web tool's returned representation, not hashes of original remote page bytes. Their SHA256 values are respectively `db878209e08c25ff17124ea1a00ab0ed03ff90f381045bd8f908d6c61e6b2a2b` and `ee4179c59abc53230099b5ffef53c0e41109ad357f4c5a0ffd8ab39774f8ca81`. Initial live searches at approximately 17:12 UTC additionally returned the HAL Anubis denial; no route retry followed. The conference/source follow-up observations use lawful public reads only.
