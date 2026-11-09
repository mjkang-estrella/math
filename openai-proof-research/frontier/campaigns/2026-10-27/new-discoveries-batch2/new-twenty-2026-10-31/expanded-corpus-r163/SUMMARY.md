# expanded-corpus-r163 summary (Claude Opus 5.5 discovery lane, 2026-11-04)

Reservation: 20 IDs (reserve7; see `reservation.json`). Deliverables:

- `results.json`: exactly 20 ID-keyed entries.
- `LEDGER.md`: per-ID ledger.
- `CANDIDATE-336565.md`: the one candidate.
- `lean/LiuDing3Design.lean`: Lean draft, UNCOMPILED.
- `outputs/registry-screen.json`: registry screen.
- Supporting files: `extracted.json` and `raw/` (exact provenance); `scripts/` and `logs/` (reproducible computations); `sources/` (fetched sources with receipts in `outputs/fetch-receipts.json`).

Lane restrictions were respected:

- No Lean, lake or SAT/ILP binaries were run.
- All computation was pure `python3 -I`, one process at a time, under `scripts/cap.sh` (120 s CPU, 140 s wall, 6 GiB RSS kill). Peak RSS observed was about 11 MB.
- No git, no child agents, no browser, and no writes outside the lane.
- The GitHub search route returned a 403; it was stopped and not retried.

## Candidate

**336565: Liu–Ding Conjecture 1 (arXiv:1707.02003).** The GA₁(2^m)-orbit of B₂ = {u : Tr(u³ − u) = 1} is a 3-design for every m ≥ 3 with m ≢ 0 (mod 4).

- **Status:** complete ordinary proof of the full conjectured scope.
- **The proof:**
  - A block-counting criterion: the design is a 3-design iff N(u) is constant.
  - An inclusion–exclusion expansion: 8N = q² − 3qs + 3s² − T(u).
  - A new quadratic identity, which makes the triple correlation T(u) factor as s·Σ_e(−1)^{Tr(u e³/(1+u)²)}.
  - That factor vanishes for odd m because cubing is bijective, and for m ≡ 2 (mod 4) because s = 0 (a GF(4) trace computation).
- **Checks:** every step was audited numerically for m = 3..10. The design property was verified for m = 3, 5, 6, 7, 9, 10, 11, 13, 14; the source's Magma range was only {3, 5, 6, 7}. The excluded cases m = 4 and 8 fail as controls.
- **Honest risk:**
  - The odd-m half is a routine Assmus–Mattson/Kasami bridge.
  - The substantive m ≡ 2 (mod 4) half rests on a short elementary argument, so a "routine" ruling is a real possibility.
  - Prior-art search was bounded: Tang 2019, Ding–Tang 2019 and Xiang–Ling–Wang 2019 bodies read, plus web searches. Ding's design book and post-2020 journal literature were not reachable.
- **Lean:** medium-high cost, not a finite certificate. The UNCOMPILED draft gives the literal endpoint `Conjecture1` and the lemma decomposition, with explicit `sorry` obligations.

## Other dispositions (no further candidate)

- **Excluded:**
  - 349834: the source was withdrawn in v2, and the only failures are at the Petersen/GP(7, ·) boundary.
  - 382445: settled by Reiswig 2024 (true for k ≤ 5, false for k ≥ 6).
  - 339995: two lines from the source's own Theorem 5.4 proof.
  - 336449: proved by the source itself.
  - 336566: routine BCH/Kasami.
- **Parked after computation:**
  - 337060: no violation for 7 ≤ n ≤ 145; a proof would rest on the Kovács–Li classification.
  - 340618: exhaustive n ≤ 4, local search at n = 5.
- **Parked:**
  - 339233 and 339234: family warning; the "if" directions are immediate.
  - 339445: search beyond the authors' length 22 is over this lane's budget.
  - Flagship, asymptotic or hard items with short source-backed dispositions: 338345, 340115, 340262, 340616, 341388, 335383, 336139, 336741, 367578.

Zero credit is claimed; root acceptance, independent review and the Lean formalization follow separately.
