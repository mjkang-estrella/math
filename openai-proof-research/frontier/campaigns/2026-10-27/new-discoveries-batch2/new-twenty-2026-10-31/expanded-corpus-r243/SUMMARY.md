# expanded-corpus-r243 research report

No eligible new solution and no Lean endpoint are submitted. All 20 reserved IDs have individual dispositions in results.json: 15 unresolved, three excluded by prior public results, one blocked by an exact-scope prior announcement, and one ineligible source-formula diagnostic. No campaign count, ledger, or other lane was edited.

The exact original JSONL lines, including newline, are under raw/. evidence/provenance.json records each chunk path, one-based line, chunk hash, raw-line hash and statement hash. All 19 distinct primary papers and every older arXiv version listed by their current abstract pages were downloaded into fresh per-request directories. Receipts retain URLs, UTC timestamps, statuses, response headers and response hashes. Text and conjecture-version inventories are retained; these are not claims of exhaustive proof-body or figure-image review.

Prior-result exclusions:

- 343333: Garg's exact Fibonacci prefix conjecture already has public Lean theorem result : claim in the Omega repository, committed on 2026-10-08 (e3ae1f5b7390f6cceec416f10578e9f507250c94). Definitions and endpoint were inspected; dependencies were not rebuilt.
- 343399: Mistri-Prajapati, arXiv:2504.09617, explicitly refutes the equality classification with {0,1,2,4,6}, h=4.
- 344693: Goryainov-Krotov, arXiv:2411.09698, Section 4.3, prints a {10;8}-CR code in H(7,3). Its strength 5 and density 4/9 violate the reserved face bound at k=2.
- 343574 is blocked rather than certified solved: Keller's author slides explicitly announce the one-corner result, but the proof body was not recovered.

The strongest sustained exact searches were:

- 344313: all t and n=2..8 for m=2 and m=4; additionally n=9,m=4,t=2..9. All geometric-chain counts agree with the source formula. The n=9,m=4,t=2 case enumerates 7,838,298 objects. An earlier t=1 case hit the CPU cap and is not counted as completed.
- 344055: all 3-uniform hypergraphs through order 6 (starting at order 4), all mixed-rank hypergraphs with edge sizes at least 3 on orders 4 and 5; 168,000 seeded 3-uniform samples across orders 7..20; 180,000 completed mixed-rank samples across orders 7..15. No counterexample. A mixed-rank order-16 partial run hit the CPU cap and receives no completed coverage.
- 344577: all labeled graphs through order 6, including 6,580 connected chordless graphs; 420 randomly completed maximal chordless graphs on orders 8,10,12,16,20,24,30. No counterexample. The larger-order sample is biased, not canonical exhaustive coverage.
- 343214: exact image sizes and full affine stabilizers for all coprime ell at (p,m)=(3,5),(3,7),(3,9),(7,3),(11,3). Every stabilizer was trivial. These diagnostics leave a uniform stabilizer lemma open; several smaller cases overlap source verification.
- 343948: 1,130,629 multisets of independent sets over six cycle parameter pairs, all with a full rainbow independent set. These do not settle the unbounded claim.

The Morse-link scan (343470) found v5(L_785)=9 against the printed prediction 8, independently checked by full integer paths and the source's finite-height transfer method. It is self-excluded as a source-formula diagnostic; see MORSE-DIAGNOSTIC.md. No formalization effort was spent to turn an ineligible computation into a nominal Lean result.

Live registry receipts lock Lean Pool to 01db1d7049cf9668bda1e9e106875ee1278b43e6, OpenAI/math to 4eaee87548250b2682affda7d05d947c05554bae, and Omega to c5efc58c550dbeeb89f2f8190e7d8106bd498efa. Complete scoped path inventories were obtained for Omega D5 and Problems and OpenAI preprints after recognizing that recursive root listings were truncated. Lean Pool projects.yml and candidates files were screened. Five bounded GitHub repository searches were retained, including focused source-ID queries for the three sustained leads. Repository metadata/path screens do not establish absence of an obscure proof. See outputs/registry-screen.json for exact scope and limits.

No 403/429/challenge was retried, redirects were not automatically followed, TLS verification stayed enabled, and denied services were not directly accessed. The initial Lean Pool projects.yml root path returned 404; its correct LeanPool/projects.yml path was then obtained from the tree. Literature search result snippets are distinguished from fetched primary bodies. Current MathDB comments/solutions were not accessed.

Every numerical search used scripts/cap.py: one process at a time, two allowed CPUs, 120 CPU seconds, 140 wall seconds, 6 GiB address-space cap, MALLOC_ARENA_MAX=2. Full stdout and resource logs are retained. A missing networkx import was replaced with standard-library Tarjan code; no packages were installed. No Lean process, child agent, browser tab, git command, publication, or external message was used. No research subprocess remains running.

This is a bounded investigation, with explicit unresolved semantic and mathematical gaps per ID. It does not claim worldwide novelty clearance, full inspection of all citing literature, a several-hour proof audit of each target, or fulfillment of the campaign's requested new-solution count. CANDIDATE.md identifies what remains worth investigating without presenting a qualified candidate.
