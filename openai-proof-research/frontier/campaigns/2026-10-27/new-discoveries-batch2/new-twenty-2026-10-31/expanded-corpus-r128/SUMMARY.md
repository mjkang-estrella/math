# expanded-corpus-r128 — bounded investigation handback

No accepted result and no Lean packet. Root alone adjudicates eligibility and acceptance. Exactly 20 ID-keyed dispositions are in `results.json`, with literal statements, raw/chunk/statement hashes, source-version receipts, review depth, attempts and remaining gaps. This pass has material gaps on the parked items; it is not an exhaustive literature or finite-object review, and does not claim the multi-hour depth requested in TASK.txt has been achieved.

The strongest mathematical output is a complete ordinary argument for **371294**, in `continued-fraction-ordinary-proof.md`. The top three homogeneous parts of the characteristic polynomial recover an ordering's endpoints and adjacency path. Thus different orderings, except reversal, give different polynomials. A finite-grid polynomial zero bound gives delta(N,n)=O_n(1/N), proving the conjectured limit for every fixed n. This is not formally certified. Its short bridge from the source's explicit formula to classical polynomial zero counting may fail the campaign's substantive-credit standard. Root should decide that gate before any Lean investment. Full literal formalization would still need the Gauss–Kuzmin/continuant semantics, arbitrary-n polynomial argument, counting, and limit; no surrogate theorem is supplied.

Source and prior-art findings:

* **366467:** public Omega full-scope S21 proof; the source identifies S22 by reverse-complement. Current pinned definitions and proof body read. No local replay of the external Lean dependency closure.
* **373088:** printed obstruction already contradicts the source's own statement that C3, P3 and P4 realize (1,1). A literal refutation is a zero-credit source correction.
* **382367:** v1 rank-coverage conjecture replaced in v2 by a weaker generic-USP conjecture. Do not silently continue the obsolete stronger target or substitute the new question.
* **370568:** public `reuellee/finite-certificates` capstone declares max f0(3,5)=42, refuting the conjectured 44 and source Proposition 6.5's tightness. The pinned proof exposition was read. Its certificate library/audit was not downloaded or replayed, so this is an explicit prior-refutation lead, not our independently verified theorem.

Finite searches with full outputs:

* **366645:** exact weighted prefix DP for all three-row standard tableaux through n=24. Both alpha and delta distribution identities hold. All totals match the hook-length formula. The cumulative run completed n<=23 before its wall cap; the separate n=24 run completed in 73.01 seconds, sampled leader RSS about 473 MB. Neither result is an all-n proof.
* **366635:** k=5, 42 Dyck words, 1,000,000 constrained local swaps. Best duplicate excess 30 among 462 k-subsets; no decomposition or infeasibility proof. A second restricted MILP had 10,412 candidate columns and 504 exact-cover constraints; HiGHS reached its 100.02-second limit with no feasible solution. This neither proves infeasibility of that model nor covers all permissible permutations. Full output: `logs/wreath-milp.log`.
* **375163:** all increasing Boolean functions and all ordered pairs in dimensions 1 through 4; 28,224 pairs at n=4. Exact integer Walsh-transform check, no failure.
* **375294:** GF(64), all 3,969 conics (t,A t+B t^2), A,B nonzero; all three nonzero norm classes and both replacement exponents. All 23,814 replacements are non-arcs. This is one restricted relative-transversal configuration at q=4, not all tangent conics.
* **368814:** 120 seeded random generator sets for each of six subgroup grids up through (4,4), exact transfer restriction/transitivity closure and redundancy removal. No exceeding basis. Dense random closure tends to small bases, so this is weak coverage, not a maximum certificate.
* **370568:** 150 integer normal-form samples for each n=3 through 8, floating Qhull vertex counts. No violation. These approximate diagnostics preceded the public-refutation lead and are not exact certificates.
* **371294:** full subset/order checks for (n,N)=(4,25),(5,15),(6,12),(7,10),(8,9); independent sparse-polynomial coefficient tests through n=10. The first three sweeps are below the source's published coverage; the latter two extend n only.

The remaining analytic, D-module, intersection-theoretic, spectral-sequence and quiver-arrangement items are parked with explicit missing models/lemmas. No finite checker was fabricated for those invariants. The mirror-Markov route remains parked on branch normalization and a uniform positive a_l; its known Fibonacci/Pell cases do not settle the full statement. No counterexample was claimed on these parked routes, and their explicit-example/classical-catalogue prior-art gaps remain open.

Provenance and access:

All 20 raw lines, including terminal newlines, are under `raw/`; one-based chunk locations and hashes are in `extracted.json`. All 26 advertised arXiv versions across the 20 sources were fetched as PDFs with dated URL/status/hash receipts; targeted version comparisons were made for the multiversion papers. Target excerpts and full PDF text are retained. Author-hosted continued-fraction journal and published wreath paper were separately retrieved. This does not mean every page of every paper was technically reviewed.

Live GitHub `/commits/HEAD` receipts: OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae` (unchanged), Omega `6c90974127979efe1615cea5d287f97d438ea712`. Complete untruncated Omega D5 and Problems trees fetched. OpenAI cached preprint path screen reused with its byte hash; no full-repository proof audit claimed. Grouped live web search outputs are under `outputs/web-search-*.json`; title/abstract leads are distinguished from actual primary-body evidence. No 403/429 response occurred in this lane; a guessed prior-art TeX path returned 404 and was not retried. No arXiv search API, denied publisher route, browser tab, git command, upload or external message was used.

Reproduction:

Run scripts from the workspace with `python3 -I <lane>/scripts/limited.py NAME python3 -I <lane>/scripts/SCRIPT.py ARGS`. The wrapper retains stdout/stderr and receipts, restricts affinity to two CPUs, CPU to 120 seconds, AS to 12 GiB, wall to 140 seconds, and samples the leader's RSS against 6 GiB. This is not a cgroup or transient/descendant-memory guarantee. MALLOC_ARENA_MAX=2 is supplied. One heavy process ran at a time. Third-party numerical libraries are existing read-only installed packages explicitly imported from the local package path; no package installation or downloaded-code execution. C++ build attempt failed because g++ was absent; the actual tableau searches use the retained Python DP. No Lean process ran, so no compiler/replay/axiom audit or upstream-cache-trust claim is made.
