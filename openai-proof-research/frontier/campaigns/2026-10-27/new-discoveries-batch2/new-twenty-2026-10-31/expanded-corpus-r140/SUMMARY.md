# expanded-corpus-r140 (Claude, reserve7): summary

Lane: 20 reserved MathDB IDs (reservation.json, reserve7 rule). The investigator worked alone with no child agents, wrote only inside this lane, and ran no Lean, lake, SAT/ILP or compiled helpers. All numerics were `python3 -I` under `scripts/limited.py`: 2 CPUs, CPU 120 s, wall 140 s, sampled RSS 1.5 GiB, address space 4 GiB, `MALLOC_ARENA_MAX=2`. One process ran at a time. One looped shell command overran its 600 s foreground timeout, was moved to the background by the harness and was stopped with TaskStop. No process was left running.

**Outcome: no candidate.** 0 of 20 proposed for credit. Three IDs are excluded as settled in the source or public literature, one is an alias, and 16 are parked. Credit is zero unless root accepts; this lane does not self-accept.

## Provenance

* `scripts/extract.py` (copied from r139, with lane name changed) wrote `extracted.json` and `raw/<id>.jsonl`. These hold each exact raw corpus line (newline kept), its one-based line number, the chunk path and chunk sha256, the raw-line sha256 and the statement sha256.
* `history-matches.txt`: grep of campaign md/review/results/ledger files for the IDs and titles. It found only the r140 launch note (ledger line 10795) and spurious hash-digit substrings. A topic-keyword grep found no earlier lane on these problems.
* Sources: `sources/abs-receipts.json` (arXiv abstract pages, HTTP 200, sha256, UTC), `sources/abs-extra-receipts.txt`, `sources/pdf-receipts.txt` and the PDFs with `pdftotext` text.
* Registries, fetched 2026-11-04 via `/commits/HEAD` (`sources/registry-receipts.txt`):
  * OpenAI/math HEAD 4eaee875… (unchanged).
  * Omega HEAD **391cceedf7cee772b9534ca84bf731e5caf08a54**, which has moved past root's 86172888. The complete Problems tree (1709 entries) and D5 tree (13824 entries) were fetched, both untruncated. The path screen found only `Problems/gupta-2026-miura-residual-degree-conjecture-83.md` and the companion `gupta-2026-miura-grid-dispersion-inequality-4.md`, both read. They concern Gupta's Conjecture 8.3 and a companion paper, not the 375834 statement.

## Dispositions

| ID | Outcome | Basis |
|---|---|---|
| 375500 | excluded: source-refuted | Jiang–Tancer (arXiv:2606.23193) disprove the Cheong–Goaoc–Holmsen conjecture in R^{3n}, n ≥ 2 |
| 375834 | excluded: source-proved | the statement is Proposition 11.8 (with proof) of the current arXiv:2607.05567**v3**; MathDB copied a conjecture label |
| 376132 | excluded for credit: public resolution for large m | Lin–You arXiv:2609.00944v2 (Sept 2026), Theorem 1.3: true for all sufficiently large odd m, with a non-explicit constant. Our exact small-m checks are below |
| 370230 | alias of 370007 | identical Kashima–Škrekovski–Xu Conjecture 3, restated in their outerplanar paper |
| 368931 | parked after sustained computation | see below |
| 369320 | parked after bounded search | ABKZ, partition-matroid instances only |
| 341534, 352140, 367512, 368493, 368505, 370007, 371865, 371866 | parked | open; no finite certificate route within the caps (reasons in results.json) |
| 347323, 369198, 371703, 374744, 375141, 376330 | parked: flagship, structural or analytic | short source-backed disposition |

## Sustained routes

1. **368931 (star decomposition for k-triangulations on the half-cylinder, general k).** I built a full model from the source definitions: lift to Z, edge classes with length in (k, kn], periodic maximality, Definition 2.6 angles and k-stars.
   * Validation: k = 2 reproduces the source's Theorem 3.6 and the counts C(2(n−1),n−1)².
   * k = 3: naive exhaustive enumeration through n = 3; flip-component BFS through n = 4 (8000 triangulations) and partially at n = 5 (16 065).
   * k = 4: n = 2, 3 (16, 1296). k = 5: n = 2, 3 (32, 7776).
   * Every completed count equals the source's conjectured C(2(n−1),n−1)^k (Conjecture 6.7). Every triangulation has k(n−1) relevant edges (Conjecture 4.5).
   * There were **0 failures** of Conjecture 3.8 across about 8.1 × 10⁵ relevant angles. The MathDB paraphrase drops the k-relevance condition; that variant also holds in the tested range (k = 2, n ≤ 4; k = 3, n = 3).
   * A bug in the first optimized run (cyclic key of v) produced spurious "0 stars" reports. It was found by validation against the k = 2 theorem and fixed before any result was used.
   * Missing for a proof: a general-k translation-exchange lemma (the analogue of Lemmas 3.3 and 3.5).
2. **376132 (tree–cycle Ramsey threshold).** Exact hereditary vertex-extension search with an exact isomorphism test, cross-validated against an independent canonical-form version and against known values.
   * m = 5 holds completely (n = 3, 4, 5 computed; n ≥ 6 by HZC Theorem 5).
   * m = 7: n = 5–8 for all trees; n = 9 for 5 of 47 trees.
   * m = 9: n = 6, 7 for all trees.
   * No counterexample. The open small-m remainder is listed in results.json.
3. **369320 (ABKZ).** About 2.0 × 10⁵ evaluations on bipartite multigraphs (two partition matroids), k = 2, 3, 4, with hill climbing. No failure; the minimum slack found is 0.

## Outputs and scripts

* `outputs/multitri-368931.json`, `outputs/treecycle-376132.json`, `outputs/abkz-369320.json`.
* `logs/*.log` with `*.receipt.json`. Some receipts record CPU-cap kills; those runs are reported as partial.
* `work/mt2-*.json`: resumable BFS states.
* Scripts: `extract.py`, `fetch_abs.py`, `limited.py`, `multitri.py`, `multitri_flip.py`, `mt2.py`, `mt2_literal.py`, `treecycle.py`, `abkz.py`.

## Lean packet

None. No endpoint was proved or proposed. All numerical results are diagnostics.
