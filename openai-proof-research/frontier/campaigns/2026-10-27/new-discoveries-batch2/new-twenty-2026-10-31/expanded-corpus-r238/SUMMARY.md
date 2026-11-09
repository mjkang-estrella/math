# expanded-corpus-r238

**No new solution or Lean endpoint. Seven exclusions and thirteen parked records. Credit: zero.** No ledger counts were changed.

`results.json` contains exactly the 20 reserved ID-keyed entries, each with the literal statement, raw/chunk/statement hashes, one-based corpus position, source PDF hash, receipts, actual review depth, attempts and remaining gap. `CANDIDATE.md` explains the strongest routes and why none qualifies.

## Prior resolutions and withdrawal

- **345099:** current source Theorem 3 proves a stronger form of the non-crossing ELP-cut claim. Chen et al. also published the resolution in *JCTB* 150 (2021).
- **352624:** Smoot's cited paper already proves the Andrews–Paule congruence; the corpus TeX is corrupted and was preserved literally.
- **352854:** Chen–Lin's cited paper proves the symmetry bijectively and cites Andrews–Chern's earlier algebraic proof.
- **355810:** Beaton–Cameron, cited source Theorem 2.9, proves the full bound and equality classification.
- **345811:** Chakraborty–Joseph–Roy–Singh, arXiv:2401.04683v4 Theorem 1.1, proves the forest formula; published in 2025.
- **345751:** Wang–Wang, arXiv:2609.15081 Theorem 1.1 (14 September 2026), refutes the universal arithmetic-graph claim with chi(B205)=206. This prior proof's computational inputs were not replayed here.
- **345931:** the imprecise universality conjecture occurs in v1/v2 but was removed in v3; excluded under the task's withdrawal rule.

## Sustained exact diagnostics

- **Trees (352551):** every unlabelled tree through order 17; 48,629 trees at order 17. Matching-polynomial spectra, minimal full-cover walk coefficients, then full-cover traces through length 102 separated all ordinary cospectral pairs. Logs and direct-walk validation retained. No high-order cospectral pair.
- **Permutations (374657):** all permutations through S9; no negative Gao coefficient. Independent transition/Macdonald validation through S5, unoptimized and optimized results agree through S8. Full S9 run finished within the individual CPU/wall caps.
- **Polygons (345516):** exact integer local search for five side-count pairs; no violation. Full counts and best witnesses in `polygon-coverage.json`; stochastic search is not exhaustive order-type coverage.

The other records are explicitly parked, with no invented exhaustive searches. Source recovery prevents the local-antimagic classification from being searched faithfully. General differential-operator recurrence and heptagon wording failures are not claimed as discoveries. The first source-unresolved feedback-grid size is T13, with 273 edges; a naive edge-mask game search is inappropriate. CMPP size at most 23 is already proved for all abelian groups.

## Sources and registry limits

All 20 original arXiv abstracts and current PDFs were retrieved. Every older version listed by those original abstract pages was retained separately. Important follow-up manuscripts and publisher/author copies were fetched and hashed. All HTTP retrievals have immutable `*.receipt.json` files. `sources/web-search-*.json` retains the discovery search outputs; snippets are leads, not substitutes for inspected primary bodies. An initially mistyped neighborhood-followup arXiv ID fetched an unrelated page; it is retained but not used as evidence. The correct paper is 2401.04683.

Current registry heads were checked: OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`, Lean Pool `01db1d7049cf9668bda1e9e106875ee1278b43e6`, Omega `ddbea3140a71acfb62e7c375dad570b7fb78ddb3`. Truncated repository-wide trees were supplemented with complete OpenAI preprints and Omega D5/Problems listings. Lean Pool's requested root projects.yml returned 404; tree discovery located `LeanPool/projects.yml`, fetched at the pinned current SHA. Candidates metadata and eight total GitHub repository-search queries were screened. No matching prior endpoint was identified in this bounded screen; no universal registry clearance is claimed. See `registry-screen-final.json` and raw receipts.

No denied Crossref, Semantic Scholar, arXiv search API, ScienceDirect, DBLP, MathDB or Palomar route was requested directly. TLS verification remained enabled. Search-engine results that mention denied publishers were retained as leads only. No browser tabs, external messages, publication, uploads, git operations, child agents or writes outside this lane were used.

## Reproduction and execution limits

Use real script paths and `python3 -I -B`. `scripts/limited.py` applies two-CPU affinity, CPU 120 seconds, wall 140 seconds, sampled RSS 6 GiB, address space 12 GiB, and `MALLOC_ARENA_MAX=2`; logs and resource receipts are retained. It monitors the process RSS, not a cgroup-wide transient peak. Numerical outputs are diagnostics and have no Lean trust status.

The C++ polygon build failed because g++ is unavailable; the Python implementation completed instead. Two refinement setup errors were corrected, retaining failed logs. One initial S9 run briefly overlapped tree refinement for approximately 20 seconds because the latter had not yet returned completion; the S9 process was terminated and rerun serially to completion. This is an execution deviation from the one-heavy-process rule, not a claim of perfect scheduling compliance. Individual processes remained capped. No background process remains at handback.

No `sorry`, axiom, surrogate theorem or bounded-diagnostic Lean endpoint was produced. Further work requires a new mathematical mechanism, not acceptance of these searches as proofs. This is a bounded research pass, not an exhaustive literature or semantic review of the reserved problems.
