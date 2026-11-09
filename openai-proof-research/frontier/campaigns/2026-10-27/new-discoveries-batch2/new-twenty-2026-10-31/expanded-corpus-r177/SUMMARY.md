# r177 final research report

No qualifying new discovery or Lean-certified endpoint survives this pass. The 20 reserved IDs have individual source-faithful dispositions in results.json: seven excluded by prior public results, twelve parked with explicit gaps, and one ordinary proof retained without credit because it is a short classical bridge.

## Candidate verdicts

- **359474 — ordinary proof, uncredited.** CANDIDATE.md gives a full traceability proof in the source's intended class. For unequal clique sizes, trace-closure first completes the high-degree class; an original cross-edge count forces a low-vertex degree gain, after which the closure is complete. Equal sizes are already source Proposition 5. The argument uses classical closure plus a short counting observation and source machinery. Its credit risk is high and likely disqualifying under this assignment. It has no literal Lean endpoint, independent review, or acceptance. It is not presented as a strong credit-worthy lead.
- **357873 — excluded, already publicly refuted.** Roy–Saha, *On the homological shifts of cover ideals of Cohen-Macaulay graphs*, arXiv:2506.01810v1, Theorem 2.7, refutes the target and the motivating exponent-one theorem. Actual theorem and proof read. The lane independently found small order-dependent failures and an order-independent square obstruction, but neither can earn new credit on this already resolved target. The search-result attribution “Kumar–Kumar” was incorrect; the downloaded primary PDF identifies Amit Roy and Kamalesh Saha.
- **358940 — no counterexample.** Exhaustive exact coefficient tables for all permutations at n=11,12,13 have no negative gamma coefficient. This extends the source's stated n≤10 verification range, but is not a full-scope proof.

No strong lead survives the credit/prior-art screen, so no Lean packet was fabricated or expensive formalization attempted. All computational algebra conclusions remain diagnostics, with no claim of a kernel-certified Tor/shift semantic bridge.

## Prior public resolutions

| ID | Primary resolution inspected |
|---|---|
| 357873 | Roy–Saha, arXiv:2506.01810v1, Theorem 2.7 and proof: whiskered even cycles |
| 357904 | Amdeberhan–Andrews–Ono–Singh, arXiv:2312.02933, Theorem 1.2(1), Corollary 1.3, proof Section 3.3 |
| 358882 | Current arXiv:2306.13521v2, Theorem 1.5 and its proof: nonuniqueness near p=6; revised conjecture only near p=2 |
| 359107 | Source arXiv:2307.05835v2, Sections 4–5: Forking Path counterexamples |
| 359120 | Current arXiv:2307.06155v5, Section 4.2.2 and Lemma 5: explicit counterexample to Expand characterization |
| 359268 | Kupers–Miller–Patzt, arXiv:2609.12951v1, Theorem A explicitly includes Out images; Section 5.1 proof inspected |
| 359504 | Haslegrave, DMTCS 20:1 (2018), *Proof of a local antimagic conjecture*; published proof downloaded and inspected |

Finiteness problems 358134 and 359132 have significant later partial progress (arXiv:2603.11883 and arXiv:2610.19014), but these were not misreported as full resolutions. The 2026 Morita paper was checked beyond its abstract specifically to settle the Aut-versus-Out scope question.

## Exact finite coverage

- Pinnacle counts: all 11! = 39,916,800 permutations, 252 nonempty pinnacle sets; all 12! = 479,001,600 permutations, 462 sets; all 13! = 6,227,020,800 permutations, 924 sets. The n=13 run uses 12 disjoint first-value shards and reversal symmetry, reflecting inverse-descent coefficients. All coefficient vectors are retained. Independent Python integer arithmetic checked factorial sums, coefficient symmetry, gamma decomposition, and nonnegativity. See outputs/pinnacle*.json and outputs/validation.json.
- Traceability: all labeled degree-sequence realizations for (m,n)=(2,3),(2,4),(3,4),(3,5),(3,6),(4,4), with 7,13,553,3211,13621,19355 realizations respectively. Disconnected-clique instances excluded. A timed prefix of 70,520 realizations for (4,5) is explicitly **not exhaustive**. Hamilton paths checked using a subset dynamic program. No counterexamples.
- Cover ideals: increasing edge-mask prefixes through first failures for three pairs through power 4 (14 admissible CM graphs; 205 shift checks), and four pairs through power 2 (31 graphs; 259 shift checks). These are early-stopping searches, not full 64/4096-mask coverage. Eight admissible labelings of the six-vertex diagnostic were checked. A first invariant-syzygy search used its 105-second internal stop on the first large case; no broad coverage is claimed. A filtered search then found an eight-vertex square obstruction after two admissible graphs and nine checked shift ideals. That filtered search omitted bipartite and whisker cases based on positive source claims subsequently shown false by Roy–Saha; those omissions are a search limitation, not mathematical clearance.
- Colorful Helly: d=1, all chordal graphs on 3,4,5 vertices (8,61,822 graphs), all uniform rank r≥2 matroids and valid m,k parameters: 56,854,18906 cases. No counterexamples. No arbitrary-matroid or d≥2 claim.
- Internal partitions: all labeled simple regular graphs on 2–6 vertices (2,2,8,14,172 graphs). Exact exception counts retained. Finitely many exceptions do not refute the finite-exception conjecture.
- Signed frustration: all 3,27,729 signed simple graphs on 2,3,4 labeled vertices, counting absent/positive/negative edge states. Criticality checked by all switchings. This does not certify irreducibility, indecomposability, loops, parallel edges or membership in L*.

No misleading finite test was substituted for graphon universal inequalities, real-matrix existential feasibility, arbitrary stochastic output channels, geometric optimal constants, categorical finite generation, or an eventual/all-but-finitely-many assertion. Those searches were not run; the precise unresolved mechanism is stated for each ID.

## Source and registry audit

Exact raw JSONL lines, including newline, are preserved in raw/. extracted.json binds one-based corpus line, chunk hash, raw hash and statement hash. History was searched by every ID and exact title in campaign prose/review/result/ledger files; no substantive older disposition of these targets was identified in the returned matches. Incidental digit occurrences in hashes and numerical arrays are not historical research hits. Ledgers and inherited exclusions were read without edits.

All current source PDFs and every earlier arXiv version listed on the 20 abstract pages were downloaded; outputs/*-source-context.txt records target/neighboring conjecture contexts across versions. This is not an assertion that every proof in every version was exhaustively audited. Source proof-body depth is item-specific in results.json. Literature searches used source IDs, titles, authors, conjecture phrases, later/citing work and selected 2026 queries before exhaustive searches. The cover-ideal refutation was located during the deeper follow-up search, before any formalization or novelty claim.

Live HEAD receipts:

- Lean Pool: 01db1d7049cf9668bda1e9e106875ee1278b43e6. Downloaded LeanPool/projects.yml and all ten candidates files. The initial root projects.yml URL returned 404; corrected using the actual tree path.
- OpenAI/math: 4eaee87548250b2682affda7d05d947c05554bae. Cached preprints path scope bound by SHA-256 at this unchanged head.
- Omega: d9631873d125955c8434f12e8695256148a72857. Fresh D5 and Problems path trees fetched. Pinnacle keyword hits were read and concern Liang–Sagan middle-order lattices and tree bottom-pinnacle uniqueness, not inverse-descent gamma positivity.

Exactly eight GitHub repository searches were spaced by eight seconds. No matching proof was found in that bounded query set; false positives and actual source scopes are recorded. No global proof-body clearance is claimed. Lean Pool's Guth–Katz joints repository is not asserted to imply equality of all optimal joints constants. See outputs/registry-screen.json and URL/status/time/hash receipts in sources/.

The closure-primary PDF route failed TLS verification. Verification was not disabled; the failure receipt is retained. An independent primary path-closure paper was downloaded through a different host. No denied HTTP route was retried, and no browser tabs, accounts, uploads or messages were used.

## Reproduction and limitations

Run from this lane using real script paths. Every numerical run should be wrapped as:

    python3 -I scripts/limited.py NAME python3 -I scripts/SCRIPT.py ARGS

For permutation enumeration use node scripts/pinnacle.js N under the same wrapper; n=13 shards use scripts/pinnacle13.js FIRST with FIRST=1..12, followed by scripts/pinnaclemerge.py. Each wrapper call waits for its child and writes a full log and receipt. The final wrapper pins two CPUs, limits each child to 120 CPU seconds, watches the process group at 6 GiB RSS, and limits wall time to 140 seconds. MALLOC_ARENA_MAX=2 and lane-local TMPDIR are set. Initial lightweight intake runs used a single-process RSS monitor; the process-group monitor was installed before the exhaustive searches. No cap-killed background process was restarted. A C++ attempt could not start because g++ is absent; the working permutation implementation is JavaScript. No packages were installed.

No Lean invocation, leanchecker invocation, sorry, axioms or uncertified surrogate conjecture endpoint was introduced. No full upstream rebuild is claimed. No background job remains at handback. Counts and acceptance decisions remain the root's responsibility; this lane claims zero accepted results.
