# expanded-corpus-r165 (Claude lane, reserve7, 20 IDs 329577–339813): no candidate

**Outcome.** No creditable candidate. There is no CANDIDATE file and no Lean packet. Per the Claude lane restriction, no Lean, lake or solver was run. Accepted credit is 0, proposed credit is 0, and nothing is self-accepted.

**Literal statements.** All 20 are extracted with chunk, line, chunk/raw/statement hashes in `extracted.json` and `raw/<id>.jsonl`, using `scripts/extract.py` copied from r163.

**History screen.** Prior campaign notes were searched by ID, title and arXiv ID; see `history-matches.txt`, `scripts/histctx.py` and `logs/histctx.log`. Related records were all handled earlier:
- 331534 (r138);
- 330598 and Ruckle items (r80 and r142);
- 334924 (fresh-corpus r15);
- 339810 and 339812 (fresh-corpus r20);
- 329765 and 329766 (fresh-corpus r9);
- 376135, the same fvs conjecture as 330252 (r71).

## Dispositions

### Settled or excluded (7)

| ID | Item | Disposition |
|---|---|---|
| 334808 | G_SR ≅ K_{r,s} | **True and already published:** Lenin, DAM 265 (2019) 204–205, cited in arXiv:2008.04282. The lane independently found the one-paragraph proof (NOTES.md §1). That proof is a short strengthening of the source's own Lemma 9, so it is zero credit in any case. Exhaustive search over orders ≤ 9 and the first 3,000,000 order-10 graphs found no realization. |
| 331313 | Csóka–Lo–Norin–Wu–Yepremyan Conjecture 12 | **Proved** by Wang–Wu (arXiv:2202.08123, JCTB 2024). An exact staircase check of all connected graphs of order ≤ 9 found no violation; K_n is corner-tight. |
| 331819 | Bakalarski–Zygadło Conjecture 4.4 | **Refuted classically.** With the source's ψ_k (minimum k-path vertex cover), the conjecture is equivalent to "no hypotraceable graphs exist", which Horton and Thomassen (1974) disproved. The MathDB paraphrase is also defective. See NOTES.md §2. |
| 331535 | Regular cycle (k−1)-cover | **Routine corollary** of the public cycle double cover theorem with a Lean endpoint (openai/cdc-lean `cycleDoubleCover_of_bridgeless`, found through the Lean Pool screen) plus an Eulerian decomposition. See NOTES.md §3. |
| 330216 | Bipartite Kneser Hamiltonicity | The source itself is the Mütze–Su proof (Combinatorica 2017). |
| 330252 | Planar fvs ≤ m/g | Confirmed in arXiv:2607.17983, Theorem 1.6 (read in r71). |
| 330713 | Lee–Zhang | The source proves n = 3 and records Labourie's refutation for n ≥ 4. |

### Parked (13)

- **329577.** Guo–Liu Conjecture 5.3. Exact numerics for r ≤ 7 and n ≤ 120 give stable constants dividing ((2r+1)!!)². A Christoffel–Darboux reformulation is in NOTES.md §4. There is no uniform proof, and the expected route (the source's Zeilberger method) carries a high risk of exclusion as a routine source adaptation, following the root's Guo ruling.
- **334925.** The source body was read. A slack argument rules out two-part and small bipartite counterexamples; there is no matroid enumeration.
- **330655.** The MathDB "for any ε" is trivially false for ε ≥ 1, which is a zero-credit wording defect. The intended small-ε conjecture is open.
- **330285.** The source definitions are defective: "critical" is defined via edges, and ρ⊥ is not computable from the source.
- **Hard or analytic open problems:** 334872, 339813, 329760, 329610, 330593, 330666, 331481, 331543 (also an already-credited Latin-square family), 331893.

## Registry screen

The screen is recorded in `outputs/registry-screen.json`.

- **Lean Pool:** HEAD is 01db1d70 (unchanged). The files at that sha were reused from r163 and keyword-grepped (`outputs/leanpool-keyword-hits.txt`). There were 0 ID hits. One material hit, the CDC formalizations, concerns 331535.
- **GitHub:** 6 spaced repository searches, all returning HTTP 200 with total_count 0.
- **openai/cdc-lean:** the README and Main.lean endpoint were read. The proof was not audited or rebuilt.

## Computations

All runs were `python3 -I` under `scripts/cap.sh`, one process at a time. Two order-9 dense-partition chunks hit the 120 s CPU cap and were rerun in smaller pieces. The order-10 G_SR run was stopped once prior art was found.

## Access

- No TLS bypass and no denials (403/429).
- arXiv and the GitHub API were accessed by curl or urllib with receipts in `outputs/fetch-receipts.json` and `outputs/curl-and-copy-receipts.json`.
- The McKay graph lists were copied from the r160 and r88 lanes. Their hashes match the original receipts, and the line counts for orders 2–9 match OEIS A001349 (order 10 was not counted).
- Deviation: one temporary file list (the paths of earlier results.json and SUMMARY.md files, used for the history grep) was written to the session scratchpad outside the lane. It has been deleted, and no other file was written outside the lane.

## Limits

- The bodies of Lenin 2019, Thomassen 1974 and the Wang–Wu paper were not read: they are identified from their titles, abstracts and citing text.
- The CDC proof was not audited.
- No global novelty or nonreview claim is made.
