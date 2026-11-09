# Discovery lane expanded-corpus-r244

No qualifying new solution was established. The 20 reserved records have exactly 20 ID-keyed entries in `results.json`: 9 excluded and 11 parked. No Lean endpoint, accepted result, or credit is claimed. No campaign count was changed.

The strongest numerical work was exact integer pointed e-basis expansion through order 9, exact Clar-cover enumeration through ten hexagons, and exhaustive independent-set/chromatic/connectivity checks on all labelled graphs through seven vertices. These produced no qualifying counterexample. Two extensions reached their 120-second CPU limit; their incomplete orders are explicitly excluded from coverage.

## Main findings

- **338216:** Already proved by Asinowski–Banderier–Hackl, *Flip-sort and combinatorial aspects of pop-stack sorting*, arXiv:2003.04912v3, Theorem 15(2), equations (16)–(17).
- **338303:** Both parts already proved: Boutin et al., arXiv:2006.03739, and Kennedy et al., arXiv:2409.18195, Theorems 4–5/Corollary 6.
- **338442:** Already proved by Fernandez–Hujdurovic, arXiv:2006.12826, Theorem 1.2.
- **344716, 358819, 338545:** The supplied primary sources themselves refute, refute, and prove the respective targets.
- **338351:** A public August 17, 2026 ProbXiv post already gives the universal-vertex counterexample family. The live primary post and receipt are retained.
- **359351:** The solver immediately found the path P8 at k = 3. This is a zero-credit application of the source-cited path formula, not a new research result. See `CANDIDATE.md`.
- **338449:** The named completion assertion was not located in either retrieved source version. With the source's product/sum definition it has an elementary one-element extension, so no significant result is proposed.

## Exact search coverage

| Record | Completed coverage | Outcome |
| --- | --- | --- |
| 338456 | All connected Hessenberg functions through n = 9; n = 8, 9 have 429 and 1,430 connected functions | No negative pointed elementary coefficient |
| 344793 | All free hole-free polyhexes through 10 cells; at size 10: 30,086 shapes, including 14,107 with perfect matchings | No nonunimodal Clar polynomial |
| 381476 | All 64, 1,024, 32,768, 2,097,152 labelled graphs at orders 4, 5, 6, 7; all 2 <= ell < k with ell <= connectivity, and all t >= 3 | No independent-set bound violation |
| 345059 | All labelled graphs through order 5 and every proper colour partition; 11,985 such partitions at order 5 | No rainbow induced-path failure |
| 345071 | Grid Type I/II polyominoes through 8 squares: counts 1, 1, 2, 5, 12, 35, 107, 363; diagonal degrees 1–4 over two large primes | Rank diagnostics match; no integral/full-scope proof |
| 359351 | All unlabelled trees orders 2–7, then first order-8 path; exact fixed-point defense game | P8 obstruction excluded as source-formula bridge |

Order 10 pointed e-positivity and order 11 polyhex enumeration were **not completed**. Logs retain partial progress; no complete coverage of those orders is claimed. The numerical scripts remain diagnostics, with no kernel-verified semantic bridges.

## Evidence and reproducibility

`raw/` preserves the exact corpus lines including newlines. `extracted.json` records one-based line numbers and chunk/raw/statement SHA-256 hashes. Every listed arXiv source version was downloaded into a fresh directory and text-indexed; this does not mean every line of every version received full proof review. `source-index.json` gives HTTP receipt paths, body hashes, text hashes and theorem/example/figure anchors. Per-record review depth and mathematical gaps are stated in `results.json`.

Current public heads were fetched for OpenAI math, Omega and Vilin97/lean-pool. Lean Pool and Omega trees were not truncated. OpenAI's main recursive tree was truncated; its separate current preprints subtree was subsequently fetched without truncation. Filename/topic screening is recorded in `registry-screen.json` and `openai-preprints-screen.json`. The apparent OpenAI `IndependentSets` hit was fetched at its immutable current head and concerns computational hardness, not the reserved extremal inequality. No exhaustive proof-body or worldwide novelty clearance is claimed.

Searches covered title/topic literature, later citing papers and 2026 results. `sources/web-search-*.json` preserve returned search evidence. Some search results mention denied publishers; no direct requests were made to Crossref, Semantic Scholar, arXiv search API, ScienceDirect or DBLP. Direct HTTP requests all returned 200. Redirects were disabled, TLS verification remained enabled, and HTTP receipts were never overwritten.

Run from the campaign directory, for example:

```
python3 -I -B expanded-corpus-r244/scripts/limited.py replay-independent python3 -I -B expanded-corpus-r244/scripts/independent.py 7
python3 -I -B expanded-corpus-r244/scripts/limited.py replay-pointed python3 -I -B expanded-corpus-r244/scripts/pointed.py 8 9
python3 -I -B expanded-corpus-r244/scripts/limited.py replay-hex python3 -I -B expanded-corpus-r244/scripts/hex.py 10
python3 -I -B expanded-corpus-r244/scripts/limited.py replay-polyomino python3 -I -B expanded-corpus-r244/scripts/polyomino.py 8
```

Use fresh log names when preserving replay history. All expensive mathematical processes ran sequentially under the resource wrapper: two CPUs, CPU 120 seconds, wall 140 seconds, sampled process RSS ceiling 6 GiB, MALLOC_ARENA_MAX=2. Peak sampled RSS was under 200 MiB. RSS monitoring is not a cgroup or transient-peak guarantee. No Lean invocation occurred, so no claim about Lean replay or cache trust is made.

The initial tree script failed because networkx was unavailable; a lane-local canonical tree generator replaced it. An attempted C++ build found no compiler, so the actual graph search used dependency-free Python. The first polynomial cross-check had an incorrect expected coronene polynomial taken from an indexed excerpt; the primary 2012 MATCH paper confirms the program's coefficients 20,32,15,2. The corrected self-check passes, and both logs are retained.

No child agents, git operations, ledger edits, external messages, uploads or browser tabs were used. All writes stayed in this lane. No background process remains. This is a bounded research pass with negative and exclusion findings, not a claim that the 11 parked problems are solved or comprehensively exhausted.
