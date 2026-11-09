# r147 discovery-lane handback

No eligible new solution is nominated. Exactly 20 ID-keyed dispositions are in `results.json`: 11 recommended exclusions and 9 parked targets. Root alone adjudicates; accepted counts and shared files were not changed. No Lean endpoint survived the novelty/scope screen, so no Lean or leanchecker process was run.

The main mathematical finding was a valid refutation of 331859, but its decisive construction is already printed in a companion paper. The spider with three arms of five edges has a four-round burning sequence, while the three terminal edges form a forest with burning number four and their nonterminal endpoints have pairwise distance eight. Bonato–Lidbetter, arXiv:1707.09968, Lemma 6 / Figure 4, explicitly prints the same spider with burning number four. The remaining forest argument is elementary. This is a source-ingredient bridge, not a campaign nomination. `outputs/spider-proof.md` gives the ordinary proof; `outputs/spider-verified.json` independently checks the covering sequence, temporal separation and all 216 three-round forest sequences. The source's pairwise-distance condition is interpreted for distinct indices, consistently with its own theorem; the diagonal-index typo is not used.

## Dispositions

| ID | Recommendation | Decisive evidence or remaining gap |
|---|---|---|
| 330692 | Park | Signed-shift inequality holds in exact source-derived counts for all permutations of lengths 3–9, all relevant alphabet sizes. Companion Conjecture 7.4 remains open for k >= 3. |
| 330859 | Park | Exhaustive Walsh-subset search through n = 5 after affine normalization; annealing at n = 5, 6, 7 finds no violation. Universal lower bound remains open here. |
| 330904 | Exclude | Source explicitly proves Xia's conjecture at the end of Section 2. |
| 331559 | Park | Exact UPC-cycle test through order 7; below already published coverage. A new canonical chord search beyond known ranges was not completed. |
| 331859 | Exclude bridge | Valid ordinary counterexample, but the decisive (5,5,5) spider and value are printed in Bonato–Lidbetter. |
| 334534 | Exclude | Bonamy–Morrison–Scott, *Partitioning the vertices of a torus into isomorphic subgraphs*, Theorem 1.5 is a published counterexample even under the stronger divisibility condition. |
| 327233 | Exclude | Source Theorem 2.2 and inverse-map Proposition 4.3 prove the vectorial bijection. |
| 328307 | Park | All 1,252 nonempty atlas classes through order 7 have recorded acyclic orientations and sequential decompositions. No general existence proof. |
| 328610 | Exclude | Méroueh, arXiv:1506.07056, Theorem 1.3 proves the exact uniform induced-poset Lubell bound. |
| 328750 | Exclude | Renteln's eigenvalue formula and Corollary 12 prove the alternating-sign property; simultaneous independent proof noted. |
| 328890 | Park | Inverse-sieve conjecture has unknown uniform constants and asymptotic scope; no finite refutation mechanism. |
| 329072 | Park | Eventual exact clique-decomposition threshold; bounded exceptions cannot refute existence of n0. |
| 325227 | Exclude | Anthony–Picollelli source Theorem 1.4 completely classifies D-unique complete multipartite graphs. |
| 325320 | Exclude | Gunderson–Przykucki, arXiv:1402.4462, Theorem 2 proves the full moment range, including its endpoint. |
| 326292 | Park | Classical real-weight MMS sets conjecture. Integer-weight diagnostics at n = 8, 12, 16 do not resolve its scope. |
| 326437 | Park | Exact rational inertia and simple-cycle counts through order 7 show no violation; the known 2026 constant-signature refutation concerns a different conjecture. |
| 333080 | Exclude | Pokrovskiy–Sudakov equi-n-square construction refutes the equal-class-size special case. |
| 381197 | Exclude | Bousquet–Heinrich, arXiv:1903.05619, Theorem 1 gives O(n^6) for planar graphs and k >= 7. |
| 322976 | Park | Integer-label additive coloring tested exactly on all atlas classes through order 7. Group-valued obstructions do not transfer. |
| 323179 | Exclude | Jiao's 2013 paper explicitly prints G(1,8) = G(3,10) = G(5,12) = 9 and replaces uniqueness by existence. |

## Sustained searches and mathematical limits

For 330859, a permutation prefix selects an arbitrary m_n-element subset of Sylvester rows, so its l1 norm is the Walsh l1 norm of that subset's indicator. Exhaustion for n <= 4 gives the conjectured minima. At n = 5, take the complement, of size 11. Its affine dimension is either 4 or 5. After an invertible affine change of coordinates, it contains 0 and all coordinate basis vectors in that dimension. Exhausting the remaining entries requires 462 canonical cases in dimension 4 and 65,780 in dimension 5. The minimum selected-set norms are 78 and 82 respectively, proving the diagnostic n = 5 lower bound with an ordinary affine-invariance bridge. This is a finite parameter verification, not a full conjecture solution or Lean theorem. Three separate 80-second seeded swap/annealing calls at n = 5, 6, 7 made 39,719,500, 25,766,500 and 14,905,500 proposals, attaining 78, 178 and 398. These later calls are heuristic. Parseval and elementary uncertainty bounds do not imply the requested universal minimum; no closed uniform certificate was obtained.

For 330692, the companion paper's Equations (13), (14), Definition 3.5 and Theorem 5.3 allow exact minimal-alphabet enumeration. All 409,110 permutations of lengths 3 through 9 were counted; all cumulative inequalities hold. The script checks invalid minimal negative segmentations directly through the repeated-prefix condition, rather than treating every monotone segmentation as allowed. The companion's exact count formulas suggest a binomial-transform positivity problem, but no uniform positivity proof or source-independent injection was completed.

For 328307, the search orientates each graph acyclically and backtracks over layer assignments. At each vertex the outgoing layers are exactly a prefix, while incoming layers are distinct. Thus each layer has indegree and outdegree at most one; acyclicity makes its nontrivial components directed paths. All 1,252 nonempty atlas classes through seven vertices have explicit witnesses. This is positive bounded coverage, not an exhaustive search of all orientations beyond that order.

For 322976, 326437 and 331559, the shared atlas sweep enumerates every graph class through seven vertices. The final inertia implementation uses exact rational 1x1 and 2x2 symmetric pivots. An old JSON field name contains `float_diagnostic`; it is explicitly stale and does not describe the final arithmetic. All simple cycles are counted once by minimum vertex and direction. The additive-label witnesses are stored per graph. For MMS, every sorted vector over [-2,2] with nonnegative total was checked at (n,k) = (8,2), (12,3), (16,4): 264, 953 and 2,511 vectors respectively. These finite tests are below known landscape coverage and do not establish new theorems.

The spider search fixed terminal-path semantics before testing. It found the k = 4 failure after 30 eligible structured cases and a k = 5 failure after 32; it then stopped for a citation-neighbourhood audit. That audit located the explicit published k = 4 construction, so no formalization investment followed. This pass is not a claim of several hours of computation or of exhaustive literature review: the timestamps and per-call runtime receipts are retained. The strongest routes were pursued beyond metadata screening, but no eligible endpoint was found.

## Evidence, access and resources

`raw/` preserves the exact 20 corpus lines including newlines. `extracted.json` and each result contain the one-based line number, full chunk hash, raw-line hash and literal statement hash. `sources/` retains current arXiv abstract pages, current unversioned PDFs, downloaded later primary bodies and dated URL/status/SHA-256 receipts. Current abstract version histories are recorded; all historical versions were not exhaustively compared, and no blanket retraction clearance is asserted. Source theorem statements and relevant proof portions were read; the report distinguishes this from independent verification of complete proofs.

Required AGENTS files, both campaign ledgers and inherited context were read. `outputs/context-read.json` records full-file ingestion hashes; `outputs/history-exact.txt` records the bounded historical ID search. No substantive prior ID disposition appeared in that scope; byte-count/hash false positives were discarded. This does not establish global nonreview or novelty.

Live registry HEADs were fetched using `/commits/HEAD`. Omega HEAD was `820a1cbd9690dde86753408e59b2735a929d017a`; complete D5 and Problems trees contain 13,872 and 1,713 entries, both nontruncated. OpenAI's complete preprints tree has 13,578 entries. See `outputs/registry-screen.json` and receipts. This was a path/topic screen, not universal registry proof-body clearance. No candidate is nominated on its strength.

The Ryerson PDF routes failed TLS certificate validation; the failures were retained, TLS verification was never disabled, and the companion was recovered from arXiv instead. The Canada thesis route returned 403 and was not retried or bypassed. No arXiv search API, ScienceDirect download retry, browser tab, author contact, upload or external message was used.

Every Python/numerical process ran via `scripts/run`: taskset to CPUs 0 and 1, CPU 120 s, wall 140 s, aggregate process-group RSS watchdog at 6 GiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR/cache/build. The watchdog is sampled and is not a cgroup/transient-spike guarantee. Only one heavy computation ran at a time. Full logs and exit/resource receipts are in `logs/`; failed dependency/compile starts are preserved. Initial NumPy imports failed because the cached binary extension was for a different Python; the final graph arithmetic avoids NumPy. No dependency installation was performed. No background job remains.

Reproduce an individual diagnostic with `scripts/run NAME python3 -I scripts/SCRIPT.py [arguments]` from this lane, using the exact script arguments visible in the output names and source files. The small read-only NetworkX copy in `vendor/` supplies its graph atlas; scripts explicitly add this lane-local path. Downloaded documents were treated as data, never executed. No full upstream rebuild or Lean cache validation is claimed.
