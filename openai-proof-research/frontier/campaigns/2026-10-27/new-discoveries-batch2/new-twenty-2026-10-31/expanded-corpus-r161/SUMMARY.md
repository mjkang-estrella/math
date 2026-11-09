# Expanded corpus r161 investigation

No new result is proposed for acceptance. There is no Lean packet, no acceptance claim and no change to campaign counts. results.json has exactly the 20 reserved ID keys, literal statements, raw-line/chunk/statement hashes, source receipts, review depth, search coverage and remaining gaps.

This is a bounded investigation handback, not a claim to the several-hour deep pass requested by TASK.txt or exhaustive literature review. The surviving computational routes produced no counterexample. Unsearched ranges and missing source/semantic bridges remain explicit in each entry.

## Source findings

- **349606:** Already refuted by the source's Proposition 20, citing Yan–Jin's earlier construction. Odd bouquet B3 has orientable genus polynomial 8z. The source classifies its counterexample family.
- **352006:** Wei–Zhao–Zhang–Ge, arXiv:2302.05586, Theorem I.2 and Lemmas III.2–III.3 construct n+s odd sets with s+2 odd pairs, contradicting 3s for s>=2. Construction and proof read. Published DOI: https://doi.org/10.1137/23M1586781.
- **346267:** The linked short source itself states and proves counterexamples in all dimensions >=3.
- **346765:** The actual published Ambrus–Nielsen–Wilson PDF, Discrete Mathematics 344 (2021), 112424, Theorem 1.6 gives O(N^(2/d)). Its definition comparison and cap-peeling proof were read. For d>3 this contradicts exponent (d+1)/(2d); d=4 suffices. No new credit.
- **345415:** Supplied arXiv URL is the wrong paper. Thomas's exposition reports a Fowler thesis proof, whereas a 2025 Springer chapter still calls the equivalent assertion open. The actual thesis/proof was not recovered. This is an unresolved source gap.
- **345262:** Source permits s=0, but its own PLRS theorem gives uniqueness then. This is a source-known domain correction, not a discovery.
- **345263:** Literal legality clauses allow a tiny initial collision absent from the prose's greedy interpretation. An inferred repair fails completeness in our diagnostic. No faithful semantic bridge established.
- **352535:** Current spectral source restricts k>=2 and explicitly knows the k=1 equality exception. MathDB says k>=1. Do not claim a source-known endpoint correction.
- **347650:** Source blocking set means a set not coverable by any matching, not MathDB's transversal paraphrase. Source scope prevails. The unknown eventual threshold cannot be refuted by one small violation.
- **346743:** Johnson–Liu arXiv:2311.07133 supplies the published rectangle/trapezoid equivariant bijection, acknowledged in the current source. Exceptional all-height pairs were not cleared; no whole-conjecture settled claim.

## Sustained finite routes

### 360151: spreading on grids

Implemented the source local rule: a white vertex needs at least three blue neighbors AND a blue neighbor with at most q white neighbors at that step. Independently checking forcing and percolation would be the wrong invariant.

Two exhaustive sweeps forced degree<3 vertices into each seed and rejected every smaller seed size before exhibiting a successful seed. Exact minima agree for q=3 and q=4:

| Grid | Common minimum |
|---|---:|
| 3 x 3 | 5 |
| 3 x 4 | 7 |
| 3 x 5 | 8 |
| 3 x 6 | 10 |
| 3 x 7 | 11 |
| 3 x 8 | 13 |
| 4 x 4 | 10 |
| 4 x 5 | 11 |
| 4 x 6 | 13 |
| 5 x 5 | 12 |

outputs/grids.json and outputs/grids-deep.json give masks and exact tested counts. After success at the final size for a given q, remaining seeds of that size are skipped for that q. These are exact minima, not counts of all successful sets.

A proof attempt considered stable white induced forests, paths meeting the boundary, and the observation that a degree-4 blue vertex is inactive exactly when it has no blue neighbor. The missing step is a cardinality-preserving transformation of a minimum 3-bootstrap seed into a (3,3)-spreading seed. No such transformation was proved. No surrogate Lean endpoint was created.

The published 2024 primary web body retains Conjecture 6.1: https://doi.org/10.1016/j.dam.2024.04.019. A direct local request returned 403 and was not retried. No local byte hash is invented for the web-visible body.

### 350694: betweenness-uniform blow-ups

Read source P4 inequalities, endpoint/interior module optimization and tree theorem before testing non-tree bases. Canonicalization by all vertex permutations gives all eligible connected simple bases of orders 4,5,6 with cut vertex and diameter>=3: 1,6,43 bases.

Extended search:

- order 4: 625 blow-ups, all singleton, I2, K2, I3, K3 choices;
- order 5: 18750 blow-ups with those same choices;
- order 6: 31347 blow-ups, all singleton, I2, K2 choices.

Exact rational Brandes centrality found no uniform graph. The first smaller sweep is separately logged. Larger bases, sizes>=4 and asymmetric internal modules remain unsearched. The tree proof does not provide a general weighted block-cut inequality. Its path endpoint argument cannot simply be assumed for arbitrary blocks. outputs/blowups.json is extended coverage. These are ordinary exact calculations without a formally verified checker.

### 346023: multiplier sets and cyclic tilings

Read Proposition 8 and Theorems 9–10 first. Initial prime-power-size sweeps are subsumed by Theorem 9 and explicitly receive no credit.

Second experiment: n=12,k=3,omega=144, so gcd(|A|,|B|)=12 and neither displayed Theorem 9 sufficient hypothesis applies. For A={0,...,8} union every 3-subset of {9,...,71}, excluding complete residue systems mod12, exact cover tested 39495 A and found no tiling. A complement translate can be normalized to contain 0. Other A in Z144 remain unsearched.

Even a violating tiling would need an explicit multiplier and prime-group realization to refute the reserved statement, rather than just stronger source Conjecture 3. See outputs/tiles-deep.json.

## Other bounded calculations

- **352316:** All unlabeled trees through order 14 (3159 at order 14), generated by canonical leaf extension, tested by exact closed-ball union backtracking. No burning failure. This is tiny known-range evidence.
- **345754:** Verified finite colorings through 32,64,128. Targets 256 and 512 hit explicit 1000000-node budgets; deepest branch reached 171. No unsatisfiability result. Earlier commentary claiming success through 512 was corrected.
- **345263:** Literal block diagnostic finds G2+G1=G3=3 for c=4,...,30. A separate prose-inferred interval restriction tested indices through 80 and values<=100000 for c=4,...,16: no collisions but many missing values. It is not a faithful intended definition or completeness bridge.
- **349325:** All labeled graphs of orders 4–6 with minimum degree>=4 checked for Hamiltonicity (0,1,76 graphs), no failure. Small superclass check; no torus recognition claimed.
- **346063:** Arithmetic verifies conjectured bounds for published counts m=4,...,9, including later N(9)=1066496. No new domain generation claimed.

Other rank, quotient-group, eventual spectral, matching-threshold and homological targets have high Lean cost or cannot be refuted by one finite example because an unspecified constant or eventual threshold is quantified. The actual 2024 homological published PDF retains Conjecture 6.6; its Lemma 6.5 already proves the conditional binomial algebra. That algebra is not a theorem about the actual boundary map. The rank source's typeset Discrete Analysis 2025:27 PDF retains Conjecture 1.1 and explains known d=3 cases.

## Provenance and limits

Required AGENTS.md files, inherited context and ledger family/status records were consulted read-only. history-matches.txt preserves bounded fixed-ID/title searches of campaign prose/results/ledgers, including numeric substring false positives. No earlier substantive exact-ID disposition was identified; this does not establish global nonreview or novelty.

Current arXiv abstract pages and latest PDFs were downloaded for 19 distinct source URLs. logs/source-audit.log lists versions and actual titles. This is not a claim that every historical version or every companion/cited proof was read. No route reached novelty-ready candidate status. An initial guessed rowmotion download (2303.00451) was unrelated, preserved and not relied on. The actual successor is sources/rowmotion-correct (2311.07133).

Live public registry heads fetched using /commits/HEAD on 2026-11-04:

- OpenAI/math: 4eaee87548250b2682affda7d05d947c05554bae, unchanged. Inherited preprints listing is referenced and hashed in outputs/inherited-inputs.json.
- Omega: 3a382196d3b69fec4a2ba29a7468eca5e9844034, changed. Root recursive tree was truncated, so complete D5 (13977 paths) and Problems (1733 paths) subtrees were fetched separately. Selected ID/topic path screen found no matches. This is path screening, not theorem-body clearance or a global search of differently named proofs.

Exact URL/status/date/byte-hash receipts are in sources/*receipts.json, individual *.receipt.json and registry outputs. Thomas exposition direct request returned 503; published-grid request returned 403. No denied route was retried or bypassed, no TLS verification disabled and no author contacted. Some published/prior status evidence is web-connector text only; hashes are not invented.

## Reproduction and resources

Use bash scripts/run.sh NAME python3 -I SCRIPT [ARGS]. Wrapper sets lane-local TMPDIR/cache variables, MALLOC_ARENA_MAX=2, taskset to two CPUs, CPU limit 120 seconds, wall timeout 140 seconds and sampled process-group RSS watchdog at 6 GiB. Full logs and receipts retained. Sampling does not exclude unsampled transients. All Python processes used the wrapper; heavy numerical workloads were serial.

No Lean, leanchecker or solver was invoked. No kernel-checking claim. No package installation, git, shared ledger edit, publication/upload, external message, browser tab or child agent. No background experiment remains at handback. All outputs are lane-local. Root decides acceptance; claimed credit is zero.
