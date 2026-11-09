# expanded-corpus-r119: summary

**Lane.** expanded-corpus-r119, reserve5, 20 IDs.

**Outcome.** No candidate; no Lean endpoint. No credit is claimed (zero unless root accepts), and none is self-accepted.

- Exact literal statements are extracted from the bound corpus chunks: `extracted.json`, `raw/<id>.jsonl`, with chunk, raw-line and statement SHA-256 hashes.
- The history grep over frontier md/json files found nothing; the only hits were numeric or hash substrings and the ledger reservation (`history-matches.txt`).
- arXiv abstract pages for all 20 sources, 2 prior-art abstracts and 13 e-prints are in `sources/`, with receipts in `sources/receipts-*.txt`.
- Registry HEADs (`sources/registries/receipts.txt`):
  - Omega HEAD is **4a11a6467d4b** (2026-11-03T01:40:51Z), newer than the root-known ddeafbc8.
  - OpenAI/math HEAD is unchanged at 4eaee875.
  - A path screen of the truncated Omega tree found no ID hits.

## Strongest routes (sustained)

### 1. 353203: uniqueness of PD-TAR(K_{s,t}) (strong lead, parked)

**Reduction.** A published theorem (Bong et al. 2023, survey arXiv:2406.05509, Theorem t:main) turns the conjecture into this statement: K_{s,t} is the only graph with its power-dominating sets. I encoded that exactly as SAT and solved it with cadical.

**SAT results.**
- UNSAT for every case with s + t ≤ 11 (that is, uniqueness holds), and also for (3,8), (3,9) and (4,7).
- The cases beyond the source's s ∈ {3,4}, t ∈ {3,4,5} are (3,6..9), (4,6), (4,7), (5,5) and (5,6).
- Controls: (2,t) is SAT, matching the source's K_{2,t}(e); (3,3) is SAT only through relabelled K_{3,3}.

**Partial proof.** Blocker duality pins down the minimal fort neighbourhoods. With that, the case where every minimal fort Ψ_xy is a pair implies H = K_{s,t}. The precise missing lemma is in `outputs/notes.md`.

**Lean.** A Lean endpoint would also need the TAR-isomorphism reduction formalised, which is heavy.

### 2. 361189: deficient path forests (verified one step beyond the authors)

**Method.** If T is deficient and its largest part exceeds 2m − 2 + L, then removing 2m − 1 from that part gives a deficient forest of order (m − 1)². So each level reduces to extensions of the previous deficient set plus a "balanced" candidate set, and every candidate is decided exactly by DFS. The code (`scripts/burn.c`, `burn2.c`) reproduces all of the source's counts: 47, 608, 5185, the full n = 7 Appendix-A table, and the unique (45,45,45,45,72,74,74).

**Results.**
- **n = 8 (new):** with L_7 = 56, all 87,956 deficient 8-path forests with l_1 ≥ 56 are impossibly burnable. The search closes at m = 31.
- **L_8 = 68 (new):** there is no deficient forest with l_1 ≥ 68. The only one with l_1 = 67 is (67,67,67,67,102,102,102,102), which is impossibly burnable.
- **Δ_8 = 54 < L_7:** a deficient forest that is not impossibly burnable is (53,53,53,53,53,53,82,84).
- **n = 9 (partial):** for m = 25..29, plus part of m = 30, all 37,861 deficient forests found are impossibly burnable. The run was stopped by the CPU caps.

There is no counterexample. Slack appears first at n = 8.

### 3. 361213: BCH dual distance (excluded, already published)

I found a short explicit proof that d⊥ = q − p for all s, using a Cayley-transform subline codeword, and checked it numerically for 11 values of (p, s). However, arXiv:2410.15070 (the same authors, October 2024) Theorem 3.4 with i = 1 already gives d⊥ = q − p. Zero credit.

## Other finite checks (coverage recorded in `results.json`)

- **353177 (1-Gray codes for q-decreasing words):**
  - The parity imbalance is ≤ 1 for all q ≤ 12, n ≤ 40.
  - Checked Hamiltonian paths were found for q = 2..4 with n ≤ 14 and for q = 5 with n ≤ 13.
- **360575 (0-Hecke modules):**
  - Every conjecture shape with |P| ≤ 8 is indecomposable (60 shapes at |P| = 7, 229 at |P| = 8).
  - At |P| = 9, 57 shapes were checked before the caps, all indecomposable.
  - The controls agree with the source's Proposition.
- **353451 (stressed-hyperplane relaxation):** the source's φ̃_{r,s,n} has all coefficients positive for n ≤ 13, so the conjecture holds for every matroid on at most 13 elements.
- **360345 (Tverberg partition graphs):** the d = 1 clause holds for r ≤ 6, n ≤ 12: the graph is connected for n ≥ 2r.

## Parked without a finite mechanism

- 353172: needs a computer algebra system.
- 353321: goodness quantifies over all n.
- 360681: no primitive-group library available.
- 361110: the converse direction needs non-rationality proofs.
- Complexity or famous items: 359900, 360113, 360324, 360565, 360623, 361744, 382188, 382203, 382215.

## Resources

- Every numerical process ran under `scripts/limited.py`: 2 CPUs, CPU time 120 s, wall time 140 s, RSS 6 GiB. Receipts are in `logs/*.receipt.json`.
- Capped or killed chunks are recorded as such and were never merged.
- C code was compiled with Lean's `leanc` against `scripts/libc.h`.
- SAT used the toolchain's `cadical`.
- No Lean, Java or pip.
- Intermediate D(m) binaries and CNFs were deleted; they can be regenerated from the scripts.
- No background jobs are left.
