# Reading, provenance and rights limits — T096N126 contribution review r1

## Process

This review was run as a T3-owned independent sub-agent through the authorized Factory Opus fallback. It used no nested agents. I wrote only inside `frontier/campaigns/2026-10-14/t096n126-contribution-r1/`. I did not edit shared indexes or author files, did not stage or commit, opened no PR, contacted no one, uploaded nothing, used no browser UI, and did no formal or manuscript work. I did not open the separate proof review or `t096n126-parent/proof-review-brief.txt`. `contribution-review-brief.txt` and `task-status.json` were read. Exact hashes of every relied-on input are recorded in `inputs.json`, and `verify.py` re-checks them read-only.

## Author packet (fresh-analytic-discovery-r126)

* Read in full: `packet/public/FROZEN.md`, `proof.md`, `operation-comparison.md`, `author-checks.md`, `reading-limits.md`, `noise-feasibility.md`, `prefreeze-addendum.md`.
* Displayed with tool clipping, and not relied on beyond their visible text: `other-screens.md`, `references.md`, `report.md`, `rights.md`, and the outside `REPORT.md`.
* Not semantically read: `source-map.json`, `verify.py`, `controls.py`, `work/catalogue.json`, `private/upstream`, `private/history` (except as listed below), `private/context`, `private/search`.
* The anchors MANIFEST/FINAL, REPORT, FROZEN and proof were recomputed and match the handoff. I did not re-run the author's verifier or controls. Those are parent artifact checks.

## Inherited project input

* `frontier/findings/R012-uniform-gaussian-propeller-stability.md`: read in full.
* `frontier/iterations/i38-inequality-stability-discovery.md`: lines 90–388 read in full (Sections 3–9, including (6.1)–(6.10), (7.1)–(7.3), Section 8 checks and the dependency graph). Lines 1–89 (screens and source interfaces) were not read. The equality/HJN machinery is inherited by reference and was not audited.
* `frontier/reviews/i38-propeller-stability-novelty-r3.md`: lines 1–80 read, plus keyword hits at lines 86–88 and 112–114. The remainder was not read.
* `frontier/reviews/i38-propeller-stability-r2.md`: not semantically read. A keyword scan returned no matching lines. Its PASS is inherited through R012.
* Source096 upstream bodies at `fd4aeeb2…`: not read. They are stipulated and enter only through the I38 contract.

## Primary texts

All primary texts were read from the author's private pdftotext copies. Their text SHA256 values match the author's register (`inputs.json`). Line numbers refer to those text files. I did not inspect any PDF visually.

1. Heilman SSC.pdf (author PDF SHA256 `6fe8cd4f…cb44`, text `47872873…2a2a`). Read: lines 1–330 (abstract, introduction, Theorem 1.2, synopsis §1.3, start of §1.4), 400–1418 (Definition 1.7, Hermite expansion (11)–(14), Section 2 including Lemmas 2.5–2.8 with proofs, Lemma 3.1 with proof, Lemmas 4.1–4.2 with proofs, Lemma 5.1 with proof, Lemmas 5.2–5.3, Lemma 6.1 statement, sketch and Steps 1–2, start of Step 3), and 1805–2284 (Theorem 7.1 with its complete proof Steps 1–4, Theorem 7.2 with proof, Corollary 7.3, Theorem 7.4 with proof, Section 8 Open Problems, references). **Not read:** lines 331–399 (Hermite preliminaries) and 1419–1804 (Lemma 6.1 Steps 3–7). The verdict does not use the bootstrap middle as a payment. It identifies the bootstrap as the dimension-dependent route that the contender expansion replaces.
2. Heilman–Tarter 2011.05583v2: lines 1–340 (abstract, introduction, Problem 1.5, Conjecture 1.6, Theorem 1.9 statement, Theorem 1.10). Section 6 and the variational proofs were not read. Theorem 1.9 is used only as stated.
3. Heilman 2306.03312v3: lines 228–442 (Theorem 1.5, stability displays, Theorems 1.6/1.8, sketch §1.4, §1.5 on four or more sets) and 2280–2330 (start of Section 8, (46)–(47)), plus keyword lines 2417–2423 near (53). Lemma 5.1, Corollary 4.2 and the rearrangement proofs were not read.
4. Heilman 2108.04950v1: lines 140–389 (Theorems 1.2–1.6, Remarks 1.7–1.9, §1.3 discussion of methods, Problems 1.10–1.11, Theorem 1.12, §1.4, start of §1.5) and 600–659 (§1.7, notation). The proofs were not read.
5. Eldan 1307.2781v3: lines 90–205 (introduction, Theorems 1–2, start of Remark 3). Section 1.1 and the stochastic construction were not read. Statements attributed to Eldan's Section 1.1 come from Heilman 2108 Section 1.1.
6. Heilman 2209.11216: only the arXiv abstract page (v1) was fetched. Full text not read.
7. Heilman 1901.03934: not read. The statement used comes from the accepted R3 record.

Milman 2403.06602v3 and Di Plinio et al. 1706.07111v1 (author copies) concern other screens and were not read.

## Bounded web search

I ran four WebSearch queries and one FetchUrl on 2026-10-19. Queries, hit titles and dispositions are in `private/search/web-search-log.md`. The hits were used for navigation only. One aggregator URL returned 404 because it was truncated, and it was not used. No exhaustive-literature or worldwide-priority claim is made.

## Rights

Original prose in `packet/public` and the outside REPORT follows the repository's CC BY 4.0 convention. `verify.py` and `controls.py` are original code under MIT. The review contains only brief quoted phrases from primary works, used for commentary with attribution. `packet/private/search/web-search-log.md` contains third-party titles and snippets. It is private, retains its original rights, and is excluded from public redistribution and relicensing. No third-party full text was copied into this directory. Primary bodies are referenced by hash in the author's private store.

## Integrity

`packet/MANIFEST.json` binds exact names, sizes and SHA256 values for every packet file except itself. The detached FINAL is the SHA256 of that exact MANIFEST file. The outside `REPORT.sha256` and the handoff carry the REPORT hash. Modes and hard-link counts are not bound. These are artifact checks, never mathematical or contribution gates.
