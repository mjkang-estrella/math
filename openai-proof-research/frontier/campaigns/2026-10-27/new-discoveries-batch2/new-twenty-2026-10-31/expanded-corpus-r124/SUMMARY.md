# expanded-corpus-r124 — investigator handback

No qualifying full literal endpoint was proved. No Lean packet was created and no credit is claimed. Root must adjudicate all dispositions. `results.json` contains exactly the 20 reserved ID keys: 6 exclusion recommendations and 14 parked routes, with literal statements, raw provenance, review depth, attempts, and remaining gaps.

## Material findings

- **341617**: the latest source explicitly reports Hiroshima's proof. Read the matching primary Theorem 4.4 and Appendix A proof reduction in arXiv:1907.10836v1. Early source labels change across versions; this is not a new open insertion conjecture.
- **341730**: the source itself proves Borwein positivity, using Theorem 12.1 for n > 7000 and Section 13 for the remaining range. Its origin is 1990, despite the reservation year 2019.
- **348870**: Upadhyay's 2021 follow-up arXiv:2101.10612v1, Theorems 1.6–1.7 and Section 5, explicitly resolves the permutation-module integrality conjecture, in the stronger signed setting.
- **348711**: the cited source itself prints the additional interval of exceptions near alpha = 2, n = 6, ell = 4. Refuting the singleton-exception paraphrase is zero credit; the corrected continuous statement was not proved here.
- **349016**: the public ProbXiv proof page already gives the ternary projective [7,3] code from two projective lines, weights 3,5,6. This is both publicly available and an elementary integrality-boundary correction. No novelty claim.
- **342382**: independent scalar and vectorized orbit computations contradict the source's stated n = 7 verification. For q = 128, s = 39, there are 16,256 distinct blocks; triples {0,1,t} occur in either 1,976 or 1,992 blocks rather than 1,984. The n = 5 exponent is Gold, and the source's own Theorem 16 gives lambda = 7 instead of the conjectured 112. Both arXiv versions print the same formula; page 20 was rendered and inspected. Treat as a source correction, not a discovery. The 2024 journal body remains unread.

## Sustained finite routes

**342383, Kassami nonisomorphism.** Implemented direct binary incidence-rank calculation over every affine image for n = 5, 7, 9, then a separate group-generator closure calculation. The latter reproduces n = 9 and extends all admissible i to n = 11 and 13. Ranks are distinct within each tested order:

- n = 9, i = 1,2,4: 19,184,46.
- n = 11, i = 1,2,3,4,5: 23,496,276,133,56.
- n = 13, i = 1,2,3,4,5,6: 27,1262,339,157,677,66.

Closure is under n binary basis translations and multiplication by a verified primitive field element. Each new independent vector is queued, and every generator image of each queued vector is reduced. The resulting invariant span equals the affine orbit span: it contains the initial block, is generator invariant, and is contained in the orbit span. Ranks are diagnostics until the implementation and field semantics are formally certified. Distinct ranks separate these finite designs, but do not solve arbitrary n or comparisons to all other APN/o-monomial families. A uniform rank/separating-invariant argument remains absent.

**347788, sparse-polynomial signs and monotonicity.** Exact integer cyclic Pascal computation, k = 1..9, all n through min(20000,128*2^k). Checked positivity in every in-range signed interval, every adjacent strict increase, and equality of the two last terms. No failures. Source only reports its sign computation through k = 5; its eventual sign theorem and first-interval monotonicity do not directly settle all intervals. The remaining uniform lemma concerns antiperiodic binomial sums, including the shifted sign sequence for adjacent differences. A heat-kernel/reflection approach was considered but not completed; no routine/nonroutine or novelty clearance claimed.

**342241, cyclic covering.** Constructed Tseitin CNF for an odd-sized induced vertex set all of whose internal outdegrees are odd, following the source's Proposition 4.1. Sampled 25 supports each at n = 13,45,47,51,53,55,57,59,61 with fixed seed 124. All 215 nonsymmetric sampled supports had a SAT bad subset, ruling them out as counterexamples. Of 10 symmetric controls/samples, 9 were UNSAT and one timed out at 0.8 seconds. Full outputs retained per instance. This goes beyond the source's exhaustive odd-order bound 43 only in **sampled** support space. No exhaustive claim about all vectors at a new order.

**342321, lens orbifolds.** Exact one-norm lattice numerator DP for every effective sign-normalized parameter triple at q = 2..30 in dimension 5: 6,048 tuples and 4,884 collisions with a previous representative. Compared all proper-divisor covers within each full-spectrum equivalence class; no failing collision. The numerator for each coordinate uses z^r+z^(q-r), including 1+z^q for zero residue, with denominator (1-z^q). This is exact equality of full rational theta series, not matching a finite spectral prefix. No general divisor-extraction proof or larger counterexample was found.

**347753, Hilbert cube.** Ran a projected Adam soft-minimum optimization with 128 starts in each of dimensions 4,8,16,32 and 6,000 steps per start. All minimum squared distances were below the proposed infinite value 0.7122844430781798. This is a heuristic non-finding, not an upper bound. Initial SciPy-dependent attempts failed because dependencies were unavailable; a NumPy-only implementation used an existing read-only package cache instead.

**348787, square-free reducts.** Enumerated 132,866 canonical nonempty ternary words through length 12, taking exact unions of terminal square-free reducts. Only cardinalities 1 and 2 occurred. This cannot establish a globally missing value, much less infinitely many. Full per-length output and witnesses retained.

## Other hard gaps and incomplete work

347823 has a material primary-statement gap: its cited single arXiv version studies matching patterns but does not locate the claimed alternating Dyck-path Mobius conjecture. No substitute order was investigated as if it were the target. 347982 needs an actual structural eventual recurrence: a finite table alone cannot disprove existence of a rational generating function with an arbitrary numerator. A new exact cell enumerator was not completed. 347387 needs actual large incidence geometries, not feasible parameter tuples or pseudogeometric difference sets. 347628 and 347632 are asymptotic growth-rate assertions with separately conjectural limit existence, so finite enumeration is not a counterexample search. 348338 is prime infinitude. 348724 remains a deep symmetric-function/statistic identity; a trustworthy full finite implementation was not completed. 351254 has a genuine asymptotic remainder beyond its source's limited Theorem I.1; small graph violations would not refute it.

This handback does **not** claim exhaustive mathematical review, a completed multi-hour search of every finite object family, or completion of the campaign goal. Actual searches and missing implementations are distinguished in each entry. No dummy Lean endpoints were generated.

## Evidence, version and registry limits

- `raw/ID.jsonl` preserves each exact corpus line including newline. `extracted.json` and each result bind chunk path, one-based line, full chunk SHA-256, raw-line SHA-256, and statement UTF-8 SHA-256.
- Read the three prescribed AGENTS files and parsed the historical/current ledgers and prior-campaign context read-only. `outputs/campaign-inputs.json` records their hashes and historical content. `history-matches.txt` is the initial fixed-string screen; `outputs/history-exact.txt` removes hash/decimal false positives. Its sole exact hit was this reservation's launch note, not an old substantive exclusion.
- All 37 listed versions across the 18 reserved source papers were downloaded with successful dated URL/status/hash receipts and converted to text; 2 follow-up papers were also downloaded. `outputs/version-review.json`, per-version target excerpts, and `old-version-labels.txt` record changing labels and target-passage screens. These are not a claim that every proof page was independently audited. The q-ary code conjecture is absent from v1 and added in v2/v3, not withdrawn later. Marberg's last version adds a resolution note.
- Live GitHub `/commits/HEAD` checks: OpenAI/math `4eaee87548250b2682affda7d05d947c05554bae`; Omega `65a253616c22829023b8ff1c09cf1d5e6a221cf6`. OpenAI matches the brief; Omega changed. The complete Omega recursive-tree retrieval hit the 140-second wall limit before a complete receipt, so **no current full-tree clearance** is claimed. No candidate was put forward as novel on the strength of an old tree.
- Dated HTTP receipts are in `sources/`; full bounded web-search outputs are in `outputs/web-search-*.json`. The first four-query web response was read but not archived verbatim; the actual pertinent primary papers were subsequently fetched and hashed. Search snippets are leads, not proof-body substitutes. No denied route was retried.

## Reproduction and resource limits

Run scripts from the workspace root using `python3 -I LANE/scripts/cap.py LABEL python3 -I LANE/scripts/SCRIPT.py`, replacing LANE with this directory. Scripts derive output paths from their own location. Fetching scripts make public HTTP requests; do not rerun automatically after denied statuses. Computational scripts are `sparse.py`, `cyclic.py`, `lens.py`, `apn.py`, `apn_scalar.py`, `kassami.py`, `kassami_closure.py`, `hilbert_adam.py`, and `reducts.py`. Direct array computations use the existing `fresh-corpus-r10/pydeps` NumPy cache read-only, with bytecode writing disabled for those scripts. The early unused SciPy script and C++ prototype are retained with failure notes; they produced no mathematical outputs.

Every expensive run used `scripts/cap.py`: affinity at most 2 CPUs, CPU 120 seconds, wall 140 seconds, sampled parent RSS cap 2 GiB, address space 4 GiB, MALLOC_ARENA_MAX=2, lane-local TMPDIR. This is stricter than the requested memory ceiling. The RSS sampler is parent-process-only, not a cgroup aggregate; solver subprocesses were small and sequential and have their own per-instance timeouts. Heavy numerical processes were run sequentially. HTTP fetch batches were limited to two workers. Logs and receipts are retained. The tree download was killed at its wall cap; other completed numerical runs exited normally. No background process is intentionally left running.

No Lean invocation or replay occurred, so no mathlib trust, leanchecker, axiom audit, or complete upstream rebuild claim is made. No git operations, shared index/ledger edits, uploads, external messages, or browser tabs were used.
