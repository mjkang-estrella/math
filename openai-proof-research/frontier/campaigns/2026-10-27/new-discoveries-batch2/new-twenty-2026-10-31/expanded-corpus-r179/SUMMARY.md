# expanded-corpus-r179 (Claude lane): summary

Reservation: 20 IDs from reservation.json (reserve8). I extracted the exact literal statements, with chunk, line and SHA-256 provenance, into `extracted.json` and `raw/<id>.jsonl`. A search of prior campaign notes for these IDs and titles (`history-matches.txt`) found only numeric coincidences, and no earlier work on any of them.

**Result: no candidate.** No CANDIDATE file was written. Every one of the 20 IDs is settled, published, deep, analytic, or parked after computation (see `results.json`).

## Sustained routes (computation performed after the literature search)

1. **353461 (Elder, nonnegative braid excess).** The conjecture says the expected number of braid moves in a uniformly random reduced word is at most 1.
   - I used an exact weak-order DP over descents: N(σ) = Σ N(σ s_k) and B(σ) = Σ B(σ s_k) + 2 Σ_{k,k+1 ∈ D_R(σ)} N(σ w0_{k,k+1}).
   - A(σ) ≥ 0 holds for **every σ ∈ S_n with n ≤ 9**. The DP reproduces Reiner's equality at w0.
   - Equality holds exactly for the longest elements of interval parabolics.
   - A stronger per-Coxeter–Knuth-class version (braid count ≤ class size) holds for every CK class with n ≤ 6.
   - No proof: Reiner's argument relies on the cyclic symmetry of R(w0), which general σ do not have.
2. **354240 (Sobolewski, Thue–Morse bound A_t(d) ≤ d+5).**
   - The exact method uses the two windows t[0,2^{K+1}) and xx, with x = t[0,2^K), together with big-integer bitset doubling.
   - The bound holds for **all d ≤ 2^15+1**. This is 8 times the authors' range of 2^12+1; even d follow from A(2d) = A(d).
   - Equality occurs only at d = 2^k − 1 with k even, up to 16383.
   - No proof.
3. **354937 (Baek, mutually interweaved laced cups).**
   - Exact reduction: it suffices to check the cap-maximal pair labellings s: (x<y) → {A, B}, with the additional WLOG s(0,·) = B and s(·,N−1) = A, plus exact forward-check pruning.
   - Exhaustive for n ≤ 5 and all k, including the first open case n = 5, k = 3 (5,799,936 raw labellings, all satisfying the conjecture). The run also reproduces Baek's k = 2 theorem for n = 5.
   - n = 6 is out of reach for capped Python; local searches there found nothing.
   - Lean Pool formalizes only the k = 2 theorem.

## Quick computational screens

- **382089** (alternating-path P+): about 112k random binary and ternary vector matroids of rank 4–6, no failure.
- **353814** (equitability): 34,710 random sparse ternary rank-5 matroids, all equitable.
- **353833** (r = 3): random search found no failure.
  - For r a power of 2, the weaker conjecture already follows from Jafari 2020 (arXiv:2009.10676, Thm 1, using ecd ≥ cd), which predates the conjecture.
  - Shaebani's Conjecture "Almost" (arXiv:2206.00836) generalizes it.

## Settled or published

- **354031** and **361332** are refuted by their own sources.
- **354402** is settled by its source (Twin-width VII).
- **354598** is reported resolved by Jung–Lew, arXiv:2504.01181 (2025).
  - My fibre decomposition gives a short proof for n ≥ d+1.
  - The literal statement fails in the degenerate case d = 6, n = 2, k = 3 (|V| ≤ d). That is a zero-credit domain correction.

## Deep or analytic (disposed of quickly)

353377 (the authors tested all of S_8), 353562, 353965, 354152, 354654, 355044, 355099 (implied by Aharoni–Berger), 355117 (equivalent to Fan–Raspaud), 361284, 370547.

## Registry screen

See `outputs/registry-screen.json`.

- **Lean Pool:** HEAD 01db1d70, unchanged. The full tree was grepped, and projects.yml contains only 2206.04260 (the k = 2 theorem).
- **GitHub:** 4 repository searches, all with 0 hits.
- **Omega:** HEAD is now da33b587, which has changed. Its tree was not screened, because no candidate was advanced.
- **OpenAI/math:** HEAD 4eaee875, unchanged.

## Resource incidents (honest record, `logs/incident-background.txt`)

- **Two backgrounded calls.** Twice I chained two `timeout 100` runs in one tool call, and the harness moved the call to the background.
  - The first finished on its own. The second was stopped with TaskStop.
  - Each Python process was still bounded by `timeout 100`.
- **RSS overshoot.** One Thue–Morse chunk peaked at 2.76 GB RSS and another at 3.5 GB, above the lane's limit of well under 2 GiB (but under the general 6 GiB cap).
  - Later chunks were shrunk, and their peak stayed at or below about 1.4 GB.
- No Lean, lake, SAT or ILP binaries were run, and nothing was written outside the lane.
