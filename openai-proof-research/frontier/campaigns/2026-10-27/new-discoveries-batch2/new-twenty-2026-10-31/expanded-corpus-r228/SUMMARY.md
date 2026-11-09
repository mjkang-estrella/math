# expanded-corpus-r228 — bounded research handback

No qualifying new solution was found. There are exactly 20 ID-keyed dispositions in `results.json`, each with zero credit and no claimed Lean endpoint. This is a bounded investigation, not an assertion that every potentially relevant paper or finite search space has been exhausted. The campaign ledger and all other lanes were left untouched.

## Strongest concrete attempts

**366415, residue-class inversion unimodality.** Exact integer computation found no failure through permutations of 24 elements (type A_23), for every k >= 3. The source [Chapelier-Laget–Fromentin](https://arxiv.org/abs/2412.19593), Conjecture 1.2 and Section 3, prints a table only through n=12. This lane used two representations:

- A full subset DP through S_21. For each subset S of positions, select the position j receiving the smallest value; add the number of earlier selected positions i with j-i congruent to 1 modulo k. This counts every permutation once.
- A compact DP through S_24, storing just the first half of each induced-subgraph polynomial. Replacing every value by its complement reverses the statistic, so each such polynomial is palindromic of degree equal to the induced edge count. Subset offsets avoid allocating the maximum polynomial degree to every subset. Unsigned 128-bit integers safely exceed 24!.

Every completed polynomial sums to N! and is symmetric. Direct permutation enumeration through S_8 independently agrees with both representations. The source's known odd-length failure at S_12, k=2 is correctly detected as a negative control. The universal unimodality conjecture remains unproved. See `logs/inversion-*.log`, `logs/compact-*.log`, `bruteforce-inversions.json` and the C/Python scripts. These calculations are diagnostics, not kernel-certified finite theorems.

**382332, unique coil griddings.** From [Bevan et al.](https://arxiv.org/abs/2410.05834), Definition 3.9, generated precedence constraints C1–C4 and enumerated total orders within each column/row. Independently enumerated all integer gridding cuts, including empty rows/columns, and checked signs and monotonicity. No failure was found in:

- All 16 choices of row/column orientation for the canonical four-cell cycle, lengths 9–12: 64 generated cases.
- All 64 orientations for the canonical six-cell cycle, lengths 13–16: 256 cases.
- All 64 orientations, six column orders and six row orders for the six-cell cycle at length 13: 2,304 cases. This includes overlap with the previous set; counts are not added as distinct cases.

The task's proposed threshold is 2 ell+1. The code has not been formalized, and this does not cover all cycle lengths. The printed length-eight obstruction and the distinct unicyclic misplaced-point example were recognized; neither was modified and promoted as a result. See `coils-*.json` and the corresponding logs.

**365508, independent sets in dense regular graphs.** Read the conjecture both in [Galvin–Marmorino](https://arxiv.org/abs/2410.19959), Conjecture 6.2, and its actual [Cambie–Goedgebeur–Jooken source](https://arxiv.org/abs/2311.00075), Conjecture 1.1. Enumerated every admissible labelled regular complement at orders 2–9 and counted all cliques, including the empty clique. Each unrestricted maximum agrees with the maximum among complements consisting of K_(n-d) components plus a remainder of order <2(n-d). The search concerns existence of a structured maximizer, not an unsupported uniqueness interpretation. `dense-coverage-corrected.json` is authoritative. The first diagnostic had an overstrong residual-degree pruning bound; it was corrected before any conclusion, and its obsolete output is retained separately.

**357335, strongly proper connection.** Built an explicit SAT encoding for K_(3,6), with variables for all three edge colors and witnesses among all simple paths. With three colors, a strongly proper path of length at least two follows one of six periodic color sequences. CaDiCaL found a coloring; an independent direct simple-path traversal verifies the coloring for all 36 vertex pairs. This is one satisfiable instance, not a proof of the general 3-connected conjecture. See `spc-K3-6.cnf`, solver logs and `spc-verified.json`.

**365677, alpha-undominated committees.** Checked 6,300 seeded random complete-ranking profiles: 300 for each candidate count 4–10 and voter count 9, 21, 51. Every size-two committee and opposing candidate was evaluated exactly. No profile had its optimum committee domination strictly above 2/3. These random instances do not target the sophisticated lower-bound constructions and give no universal result. Endpoint-equality artifacts were not counted.

**357250, paperfolding.** The published [Mol–Rampersad–Shallit paper](https://cm.episciences.org/14019/pdf), Conjecture 6.5, literally includes i=0 and hence odd lengths, which cannot be Dyck lengths. That is a zero-credit endpoint defect. For the intended even-length question, a 262,144-term regular-paperfolding prefix contains every proposed even length <=4,096 and no other Dyck length <=4,096. A separately tested complement encoding has additional lengths and is not substituted for the source convention. No general corrected theorem was proved.

## Prior results and exclusions

- **357415:** [Choi–Gan 2024](https://math.mit.edu/research/highschool/primes/materials/2024/Choi-Gan.pdf), Theorem 1.1 and Corollary 1.2, explicitly prove the Eeta-win formula. Primary PDF retained.
- **366414:** The assigned source itself refutes odd-length unimodality at n=11. Its known counterexample earns no new credit.
- **366453:** Omega already publishes `PetrovScottMultiplicityDominance.lean` and its blueprint at pinned head `6aabd0ef13314679f92b922143be5084c054f1f9`. The path's last commit, `17405edc663ecd04295edd2d5f1597a3d225a1fa`, is dated 2026-11-04 23:46:59 UTC, before this reservation. The development explicitly retains a problematic printed odd-length splitB formula, restricts to the fixed-weight matrix, and flags an unfinished audit. This lane neither independently certifies that development nor claims a new proof by correcting the source.
- **365514:** [Kaur–Kumar, arXiv:2608.08997](https://arxiv.org/abs/2608.08997), Theorem 1.4, already claims the full intended cyclotomic conjecture. Its validity was not independently certified. The MathDB odd-k clause also has a paraphrase defect; exploiting it earns nothing.
- **357250:** Literal odd-length failure is excluded as an endpoint correction; intended even-length scope remains parked.

All other dispositions, including analytic, asymptotic and flagship structural obstacles, are in `results.json`. The trivariate finite-field source has significant prior partial results; the Hardy–Sobolev–Maz'ya source itself solves k>=3 and leaves k=2. Neither was represented as a new full solution.

## Evidence, access and limits

`raw/` preserves the 20 exact corpus lines with terminating newlines. `extracted.json` records chunk paths, one-based lines, chunk hashes, raw-line hashes and statement UTF-8 hashes. `history-filtered.txt` is the bounded historical scan after removing hash-substring false hits; this is not proof that no unindexed old review exists. `governance-readonly-snapshot.json` retains read-only inherited family summaries and governing-file hashes.

HTTP responses and dated, hashed receipts are in `sources/`; `http-receipt-index.json` indexes them. Receipts were not overwritten. ArXiv abstract histories were inspected and earlier listed versions fetched. The published paperfolding PDF was essential because the arXiv HTML did not contain the full published final section. Source figure/example labels are indexed in `source-label-inventory.json`; this is textual inspection, not a claim to have visually audited every figure.

Current GitHub heads were fetched for Lean Pool, OpenAI math and Omega. Lean Pool's recursive tree was complete. OpenAI and Omega root recursive trees were truncated; the complete OpenAI preprints and Omega Problems subtrees were additionally fetched. Relevant Omega source and blueprint bodies were retrieved. This is bounded filename/body screening, not exhaustive content search or replay of every public Lean proof. Web search responses 02–10 are retained; the first exploratory search response exists in the conversation but was not saved verbatim locally. Some search hits were irrelevant and were not treated as evidence. The located follow-up `2506.22133` HTML returned 404; its body remains unread. Not all citing local-antimagic papers were inspected. These limits block any claim of full novelty clearance.

Inherited denied services were not contacted directly: Crossref, Semantic Scholar, arXiv search API, ScienceDirect, DBLP and MathDB. No 403/429 was retried, TLS verification was left enabled, and no browser tabs or external messages were used. Downloaded documents were treated as data; none of their scripts were executed or extracted into shared directories.

Every numerical process ran sequentially under the lane wrapper with two CPUs, CPU 120 seconds, wall 140 seconds, sampled RSS cap 6 GiB, and MALLOC_ARENA_MAX=2. Largest recorded RSS was about 3.71 GB, and the longest completed numerical call was 67.61 seconds. Sampling is not a cgroup or transient-peak guarantee. Missing g++, C headers and bs4 were recorded; standard-library HTML parsing and a locally compiled C shared library using Lean's clang supplied the working routes. No packages were installed. All Python invocations used `python3 -I -B` and real script paths. No Lean process or numerical background job remains.

## Reproduction

Run from the campaign directory; all writable paths remain in this lane. `scripts/limited.py NAME COMMAND ...` writes the full log and resource receipt. Use fresh NAME values to retain old logs.

- Exact graph enumeration: `python3 -I -B expanded-corpus-r228/scripts/limited.py replay-dense python3 -I -B expanded-corpus-r228/scripts/dense.py`.
- Coil tests: invoke `coils.py 2`, `coils.py 3`, and `coils-ordered.py 3` through the same wrapper.
- Polynomial shared libraries: compile the local `.c` scripts with the pinned Lean `bin/clang -O3 -shared -fPIC -nostdlib`, writing the corresponding lane-local `.so`; then run `run-inversions.py`, `run-inversions128.py` and `run-compact.py` with the parameters preserved in logs and the report.
- Independent checks: `verify.py`, then `compact-verify.py`, through the wrapper. The latter intentionally expects the k=2 negative control to fail unimodality.
- SAT: run `spc.py 6` through the wrapper, then the pinned Lean `bin/cadical` on the generated CNF; solver return code 10 means satisfiable.

The reproducible scripts, full coefficients, witnesses, resource receipts and primary-source hashes support the stated finite coverage. They do not close the remaining universal proof obligations. No acceptance, publication, paper or Lean packet is proposed.
