# Lattice search — no persistence-12 number below 10^525

**Proved (exhaustive, exact):** every 7-smooth m = 2^a·3^b·5^c·7^d with len23(a,b)+c+d ≤ 525 has **P(m) ≤ 10**.

**Claim (by notes/theory.md Theorem 3, length-domain completeness):** **no positive integer n < 10^525 has multiplicative persistence ≥ 12; every n < 10^525 has P(n) ≤ 11.**

Date: 2026-10-19 12:16:28.  

## Machine

- python: 3.14.7
- platform: Linux-7.2.8-200.fc44.x86_64-x86_64-with-glibc2.43
- cpu_count: 32
- hostname: mj-framework
- cpu_model: AMD RYZEN AI MAX+ 395 w/ Radeon 8060S
- mem_total_gb: 125.1
- loadavg: ['35.64', '44.30', '31.13']

## Method

- Domain 𝓜_525 = {(a,b,c,d) : len23(a,b)+c+d ≤ 525}, enumerated **exactly and completely**: |𝓜_525| = 19,210,237,201 points; all 19,210,237,201 evaluated (1.000000000 of domain).
- m built incrementally per (a,b) (×5, ×7 stepwise); `s = str(m)`; `'0' in s ⇒ P(m)=1` (F2, exact) else `P(m) = persistence(m)` — the shared, gate-validated library. No heuristic pruning anywhere.
- Sharded by (a, b-range) across a multiprocessing forkserver pool; every (a,b) re-derives mab, the c-chain and d-chain endpoints with independent pow() constructions and asserts equality (integrity against incremental-build drift).
- Joint (P, k=len23+c+d) counts tracked during the sweep so milestone results for every 𝓜_{D'} ⊆ 𝓜_{D} are extracted exactly from this single pass.

## Validation gates

- [x] triangle moment closed forms vs brute force (R<=40)
- [x] python3 src/test_core.py exits 0 — rc=0
- [x] D=5: max P(𝓜_5) == 6 with 27648 == 2^10·3^3 among P=6 points — best=6 at (10, 3, 0, 0, 27648), 441 pts, |P=6 ties|=1: [(10, 3, 0, 0)]
- [x] D=15: (19,4,0,6) -> m=4996238671872 present with P == 10 exactly — max P(𝓜_15)=10 at (19, 4, 0, 6, 4996238671872), 18496 pts, |P=10|=1
- [x] D=15: max P(𝓜_15) == 10 (nothing above the record) — best=10
- [x] eval_domain == scan_all at D=15 (exact N + moments) — N=18,496, rel(d1)=2.08e-15, rel(d2)=1.29e-15
- [x] eval_domain == scan_all at D=300 (exact N + moments) — N=2,065,793,401, rel(d1)=9.83e-15, rel(d2)=2.06e-14
- [x] chunk_worker == independent reference (D=15, a<4): npoints & hist & maxp — worker 5336 pts/hist={0: 9, 1: 4372, 2: 808, 3: 97, 4: 36, 5: 8, 6: 3, 7: 2, 8: 1} maxp=8 vs ref 5336 pts/hist={0: 9, 1: 4372, 2: 808, 3: 97, 4: 36, 5: 8, 6: 3, 7: 2, 8: 1} maxp=8
- [x] joint-histogram bigint packing round-trip
- [x] spot-check 250 random 𝓜_15 points: incremental==smooth(), fast==library==naive
- [x] spot-check 250 random 𝓜_50 points: incremental==smooth(), fast==library==naive
- [x] spot-check 250 random 𝓜_300 points: incremental==smooth(), fast==library==naive
- [x] spot-check 250 random 𝓜_700 points: incremental==smooth(), fast==library==naive
- [x] spot-check total — 1000 points

All gates passed: **True** (incl. `python3 src/test_core.py` exit 0).

## Rate calibration

- bench D=300, a<105: 804,762,280 pts in 49.2s → 1.957 µs/pt/core (Σd² analytic vs measured rel err 0.000%)
- bench D=550, a<11: 608,989,422 pts in 77.0s → 4.047 µs/pt/core (Σd² analytic vs measured rel err 0.000%)
- bench D=800, a<2: 342,935,601 pts in 78.7s → 7.345 µs/pt/core (Σd² analytic vs measured rel err 0.000%)
- milestone-mode overhead: +0.252 µs/pt/core; pool startup 0.10s; selected D = 525 (projected 44.6 min)

## Milestone results

| D | \|𝓜_D\| exact | max P | argmax (a,b,c,d) | m | wall |
|---|---|---|---|---|---|
| 22 | 76,176 | 10 | (4, 20, 0, 5) | 937638166841712 | 0.00 min |
| 50 | 1,758,276 | 10 | (4, 20, 0, 5) | 937638166841712 | 0.00 min |
| 100 | 26,532,801 | 10 | (4, 20, 0, 5) | 937638166841712 | 0.02 min |
| 200 | 412,130,601 | 10 | (4, 20, 0, 5) | 937638166841712 | 0.29 min |
| 300 | 2,065,793,401 | 10 | (4, 20, 0, 5) | 937638166841712 | 2.07 min |
| 400 (extracted) | 6,496,521,201 | 10 | (19, 4, 0, 6) | 4996238671872 | — |
| 450 (extracted) | 10,388,909,476 | 10 | (19, 4, 0, 6) | 4996238671872 | — |
| 500 (extracted) | 15,813,314,001 | 10 | (19, 4, 0, 6) | 4996238671872 | — |
| 525 (extracted) | 19,210,237,201 | 10 | (19, 4, 0, 6) | 4996238671872 | — |

Cross-validation: milestone 𝓜_300 histogram extracted from the single 𝓜_525 sweep **equals** the standalone complete 𝓜_300 pass (npoints 2,065,793,401 vs 2,065,793,401).

## Final result at D = 525

- **Exact domain size:** |𝓜_525| = 19,210,237,201
- **Points evaluated:** 19,210,237,201 (complete; asserted equal to the domain size)
- **Wall time:** 32.03 min on 32 workers (9.99 Mpts/s aggregate, 3.202 µs/point/core)
- **Max P seen: 10** at (a,b,c,d) = (4, 20, 0, 5), m = 937638166841712
- **P histogram (all points):** 0:9, 1:19,210,224,599, 2:11,994, 3:387, 4:142, 5:41, 6:12, 7:8, 8:5, 9:2, 10:2
- **Zero-free points:** 12,615 of 19,210,237,201 (0.000066%); their P histogram: 0:9, 1:13, 2:11,994, 3:387, 4:142, 5:41, 6:12, 7:8, 8:5, 9:2, 10:2
- **Integrity checks passed:** 3,313,804 (independent re-derivations)

### Zero-free counts by digit length

Full table: `results/lattice_zerofree_by_len.csv` (501 digit lengths, 1–501). Summary:

| digit length L | points | zero-free | fraction |
|---|---|---|---|
| 1 | 9 | 9 | 100.00% |
| 2 | 36 | 27 | 75.00% |
| 3 | 95 | 55 | 57.89% |
| 21 | 19,960 | 350 | 1.75% |
| 41 | 142,038 | 170 | 0.12% |
| 61 | 460,533 | 46 | 0.01% |
| 81 | 1,069,748 | 6 | 0.00% |
| 101 | 2,063,972 | 1 | 0.00% |
| 121 | 3,537,499 | 0 | 0.00% |
| 141 | 5,584,624 | 0 | 0.00% |
| 161 | 8,299,638 | 0 | 0.00% |
| 181 | 11,776,838 | 0 | 0.00% |
| 201 | 16,110,527 | 0 | 0.00% |
| 221 | 21,394,982 | 0 | 0.00% |
| 241 | 27,724,512 | 0 | 0.00% |
| 261 | 35,193,409 | 0 | 0.00% |
| 281 | 43,895,955 | 0 | 0.00% |
| 301 | 53,926,465 | 0 | 0.00% |
| 321 | 65,379,217 | 0 | 0.00% |
| 341 | 78,348,501 | 0 | 0.00% |
| 361 | 92,928,637 | 0 | 0.00% |
| 381 | 108,735,203 | 0 | 0.00% |
| 401 | 120,135,931 | 0 | 0.00% |
| 421 | 118,254,294 | 0 | 0.00% |
| 441 | 94,165,621 | 0 | 0.00% |
| 461 | 44,926,558 | 0 | 0.00% |
| 481 | 6,570,645 | 0 | 0.00% |
| 501 | 436 | 0 | 0.00% |

### Zero-free digit-length extremum — input to Theorem 5 (conditional resolution)

For zero-free m the digits of m themselves are a valid factorization, so len(m) ≤ dc(m); hence every zero-free 7-smooth with dc ≤ 525 lies in the swept 𝓜_525. **The sweep found zero-free 7-smooth numbers only up to dc = 140** (1 at that length; 115 distinct lengths, 12,615 total). Therefore this sweep **verifies: no zero-free 7-smooth number has 141 ≤ dc ≤ 525**, and the zero-free count is exactly 12,615 for every dc ≤ 525. With C = 140 in Theorem 5, branch 2 needs D ≥ ⌈C·log₉10⌉+1 = 148 ≤ 525 ✓ (satisfied by this result); branch 1 (dc > C ⇒ contains 0) is verified here for dc ≤ 525 and remains open only for dc ≥ 526 (cf. agent B's zero-free scan).

## The claim

> **No positive integer n < 10^525 has multiplicative persistence ≥ 12.** Equivalently, every n < 10^525 reaches a single digit in at most 11 steps.

Proof: exhaustive verification that P(m) ≤ 10 for all 19,210,237,201 elements of 𝓜_525 (complete by notes/theory.md Lemma 2 + Theorem 3), combined with P(n) = 1 + P(Π(n)) for n ≥ 10.

## Counterexample search

**No P(m) ≥ 11 was found anywhere in 𝓜_525 — no discovery, no counterexample.** The 11-step conjecture stands for all n < 10^525.

## Artifacts

- `results/lattice_gates.json`
- `results/lattice_bench.json`
- `results/lattice_checkpoint.json`
- `results/lattice_zerofree_by_len.csv`
- `results/lattice_checkpoint_D22.json`
- `results/lattice_checkpoint_D50.json`
- `results/lattice_checkpoint_D100.json`
- `results/lattice_checkpoint_D200.json`
- `results/lattice_checkpoint_D300.json`
- `results/lattice_checkpoint_D525.json`

