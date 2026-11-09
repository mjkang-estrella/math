# Failures and limits (preserved)

1. `lab321_bruteforce` v1 (runs/*_v1_cpu_capped): the first implementation had an
   inefficient second constraint pass and no WLOG f(0)=0. It hit the 210 s CPU cap
   (guard_exit −9) with no output. It was replaced by v2; v1 output is kept.
2. v2 brute force, case n=45 with 15 labels (expected: a labeling exists, per source
   Table 5): CPU cap. Inconclusive and not load-bearing.
3. Independent 15-label upper-bound replay for C_n(1,5):
   - `lab321_upper.py` raised a MemoryError under 512 MiB;
   - `lab321_upper_lean.py` hit the CPU cap.
   As a result, 372628's upper bound rests on source Theorem 24 only. The caps were
   not increased.
4. The fetch logger split content-type on spaces in its first six rows. The fields
   were re-split post hoc (noted per row); the bytes were unaffected. The logger was
   fixed to use tabs.
5. The arXiv author feed `s-author-holub` was flagged by the challenge heuristic.
   This was a false positive: the word "challenges" appears in an abstract. It was
   not retried.
6. The arXiv author query `au:Rabinowitz_S` returned an empty feed. Not retried with
   variants.
7. Search-tool summaries (WebSearch) are secondary evidence only. Claims taken from
   snippets, not from retained bodies, are labeled record-plus-search-snippet.
8. Not done:
   - no MathDB access (429 HOLD);
   - no browser use;
   - no Google, GitHub API or ScienceDirect;
   - no source bodies retrieved for the 45 rows outside the shortlist;
   - no counterexample searches for 365438, 371484, 373717, 374443 or 382271;
   - successor literature for 378132 not checked.
