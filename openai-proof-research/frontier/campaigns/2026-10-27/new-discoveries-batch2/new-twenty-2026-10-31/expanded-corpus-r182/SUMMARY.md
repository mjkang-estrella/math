# expanded-corpus-r182 (Claude lane): summary

Reservation: 20 MathDB IDs from 345158 to 371727 (`reservation.json`, reserve8 rule).

- Exact raw lines and provenance (chunk, one-based line, chunk, raw and statement hashes) are in `raw/*.jsonl` and `extracted.json`.
- History grep: `history-matches.txt`. Its only substantive prior note is the 358587 screening in `root-nearline-r1`.
- Every source abstract page was fetched for its current arXiv version. TeX was read for 13 sources and the journal PDF for 351804.
- Receipts are in `outputs/fetch-receipts.json`.

Lane restrictions were followed:

- No Lean, lake or SAT/ILP binaries were run.
- Every computation was a single `bash -c 'ulimit -v 2000000; timeout 100 python3 -I …'` call, one per tool call. One check timed out at 100 s and was rerun in two chunks.
- Nothing was written outside the lane.

## Candidate

**351804, Yang–Wang A_α conjecture for non-strongly connected digraphs.** File: `CANDIDATE-351804.md`.

An exact 5-vertex counterexample refutes the fixed-strong-component reading:

- G\* has arcs 0→1, 0→2, 1→0, 1→2, 1→3, 2→0, 3→0, with out-degrees (2,3,1,1), so v1 = 1.
- G = G\* + 0→4, and G'' = G\* + 1→4.
- At α = 1/4, ρ(G) > 781/400 > ρ(G'').
- The certificate:
  - the integer characteristic polynomial s(s⁴−8s³+4s²−24s+27) is negative at 7.81;
  - the Collatz–Wielandt weights (671,1000,296,296,1) bound the other matrix by 2309/296 < 7.81.

Supporting work:

- An exhaustive sweep over m ≤ 4, E ≤ 3 found violations only for α ≤ 0.35, and none inside the source-proved range.
- The mechanism is Perron sensitivity x_j y_j rather than out-degree.

Credit risk is high:

- The 2024 journal version (Oper. Matrices 18, 319–333) replaced the conjecture by Theorem 3.7, which proves the global reading (Kₙᵐ is the maximiser). It kept our reading only as the open question of Remark 3.8, which this example answers negatively.
- The mechanism is a generic perturbation fact.
- The example is small.

Lean cost is low. There is an UNCOMPILED draft in `lean/AalphaNonStrongCounterexample.lean`. Remaining pieces:

- a Bool checker for G_n^m membership;
- the weighted-norm eigenvalue lemma;
- the sSup bookkeeping.

Registry screen (`outputs/registry-screen.json`): no hits on Lean Pool 01db1d70, Omega 63ebfbfb (complete D5 and Library subtrees), OpenAI/math 4eaee875 or GitHub search.

## Settled with zero credit

| ID | Outcome | Reason |
|---|---|---|
| 351504 | proved by a routine bridge | The (k,H)-kernel conjecture is true for all r ≥ 2 and k ≥ r+2 (`outputs/351504-bridge-proof.md`). Take one vertex per terminal component, chosen as a reversed (r+1)-king (Galeana-Sánchez–Hernández-Cruz–Juárez-Camacho 2013). Cross-component distances are ≤ r−1, and H-length ≤ length. The new part is one paragraph on 2013 results by the same first author. |
| 352363 | source-refuted as printed | The statement is Reid–Wu–Zhou's conjecture, which N₉ (k = 4) and the RWZ (2k+1)-element examples (k ≥ 5) already refute, as the source says. |
| 365570 | source-refuted | Cichacz–Suchan disproved Tannenbaum's conjecture (survey Theorem Skol). |
| 358587 | published resolution, credited family | The circulant nut graph classification (arXiv:2212.03026) excludes n = d+4 when 8 \| d, and (16,8). The source proves the Cayley version. This is the 365943 family. |
| 352396 | source-settled | Dhar proves the Kakeya conjecture over Z/NZ. |

## Parked, with the recorded search coverage or source-backed reason

| ID | Disposition |
|---|---|
| 345726 | Prescribed-roots branchings. The checker is complete; a positive control at arc-strength 2 reproduces the source's failures. Random arc-minimal 3-arc-strong digraphs with α = 2 were tested at n = 6 (62,554), 7 (31,213), 8 (16,831) and 9 (9,448): all have good pairs for every (s,t). |
| 345158 | Ryser(r,t): first open case r = 3t. The 2026 OpenAI Ryser counterexamples are t = 1 and do not transfer. |
| 345188 | Probabilistic; no finite certificate. |
| 345562 | Reduces to a parity condition on iterates of σ(n) = s₁+…+sₙ for all h; no finite certificate. |
| 345642 | Coprime splitters follow from the published classification for k1+k2 ≤ 30 and from Leung–Zhang (2026) for k1 = 0. A counterexample would need k1+k2 ≥ 31. |
| 352072 | Gvozdenović–Laurent SDP bound: open beyond r ≤ 6. No SDP tooling in the lane. |
| 352370 | Uniform c over all k: still open per EJC 2023. |
| 352492 | Still conjectured in v4 for p > 3; uniform in n. |
| 352585, 352587 | Zero-sum family. Largely settled by Müyesser–Pokrovskiy and 4-ZSPP; family warning. |
| 352628, 352856, 359400 | Famous problems; disposed quickly. |
| 371727 | Structural clique-width; no finite certificate. |

## Files

- `results.json`: 20 ID-keyed entries, built by `scripts/build_results.py`.
- `CANDIDATE-351804.md` and `lean/AalphaNonStrongCounterexample.lean` (UNCOMPILED).
- `outputs/351504-bridge-proof.md`, `outputs/registry-screen.json`, `outputs/github-search.json`, `outputs/abstracts.txt` and `outputs/fetch-receipts.json`.
- Scripts in `scripts/`, logs in `logs/`, and sources (fresh directories per download) in `sources/`.
