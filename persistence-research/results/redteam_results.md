# RED TEAM results — subagent C (adversarial attacks + bug hunt)

Run: 2026-10-19 11:15:59 · Python 3.14.7 · 32 cores (using 16 workers) · 7789 MB available

Attacks: (1) independent heap frontier ≤ 9²², (2) preimage attack on the P ≥ 10 frontier, (3) 2.2M-sample Monte Carlo with len ≤ 600, (4) DP brute sanity to 10⁸.

---
## 0. Validation gates
- `[PASS]` python3 src/test_core.py exits 0  — (2.6s)
- `[PASS]` P(277777788888899) == 11 naive and fast
- `[PASS]` record chain matches literature
- `[PASS]` Pi(68889) == 27648
- `[PASS]` P(27648) == 6 (naive + fast)
- `[PASS]` 27648 = 2^10*3^3 lies in 𝓜_5 (witness digits 6,8,8,8,9 → len23(10,3) ≤ 5; lower bound ⌈(10+3)/3⌉ = 5 ⇒ = 5)
- `[PASS]` independent len23 builder == library on every (a,b) ∈ [0,90]×[0,60]  — (0.0s, mismatches=[])
- `[PASS]` len23 certificates (bounds + constructible witness) on 205 cells  — bad=[]
- `[PASS]` len_of_smooth(0,5,1,1) crashes — CONFIRMED BUG (reported, not patched)  — len_of_smooth(0,5,1,1) raises TypeError: 'NoneType' object is not subscriptable

## 1. INDEPENDENT FRONTIER — every 7-smooth m ≤ 9²² by min-heap generation (different algorithm from the lattice searcher)
- heap generation (seed 1, pop-min, push ×2/×3/×5/×7, set-dedupe): **118,129 numbers** in 0.1s
- `[PASS]` heap set == independent exponent-tuple enumeration (two different generators)  — (0.0s, |tuple set| = 118,129)
- P-histogram over the domain: {0: 9, 1: 113132, 2: 4423, 3: 354, 4: 141, 5: 41, 6: 12, 7: 8, 8: 5, 9: 2, 10: 2}
- **max P over 7-smooth ≤ 9²² = 10**, attained at 2 value(s), smallest = 4996238671872
- `[PASS]` max P over 7-smooth ≤ 9²² equals 10  — (< 10 impossible: 4996238671872 is in the domain with P = 10)
- `[PASS]` top-20 by P re-verified with persistence_naive  — bad=[]
- `[PASS]` 2000 random domain members re-verified with persistence_naive  — bad=[]
- `[PASS]` min{m : P(m) = 10} == 4996238671872  — got 4996238671872
- `[PASS]` 4996238671872 = 2^19·3^4·7^6 with len = len23(19,4)+6 = 15
- **P ≥ 9 frontier: 4 members** (P=9: 2, P=10: 2); len ≤ 22 subset: |F9| = 4, |F10| = 2. Full list → results/redteam_frontier.csv

| m | (a,b,c,d) | len | P |
|---|---|---|---|
| 4996238671872 | (19,4,0,6) | 15 | 10 |
| 937638166841712 | (4,20,0,5) | 17 | 10 |
| 438939648 | (12,7,0,2) | 10 | 9 |
| 231928233984 | (33,3,0,0) | 13 | 9 |
- `[PASS]` lead's new frontier member 937638166841712 = 2^4·3^20·7^5 found with P = 10
- `[PASS]` lead's 231928233984 = 2^33·3^3 found with P = 9

### Independent exhaustive maxdomain(D) scan (𝓜_D = {len23(a,b)+c+d ≤ D})

| D | my max P | my #points | lead max P | lead #points | my argmax m (P = max) |
|---|---|---|---|---|---|
| 5 | 6 | 441 | — | — | [27648] |
- `[PASS]` maxdomain(5) == 6 with 27648 among attainers (test_core equivalence)
- `[PASS]` my maxdomain(8) == lead's published 8  — mine=8
- `[PASS]` my 𝓜_8 point count == lead's 2,025  — mine=2,025
- `[PASS]` lead's D=8 argmax members all attain my max  — mine=[4478976]
| 8 | 8 | 2,025 | 8 | 2,025 | [4478976] |
- `[PASS]` my maxdomain(10) == lead's published 9  — mine=9
- `[PASS]` my 𝓜_10 point count == lead's 4,356  — mine=4,356
- `[PASS]` lead's D=10 argmax members all attain my max  — mine=[438939648]
| 10 | 9 | 4,356 | 9 | 4,356 | [438939648] |
- `[PASS]` my maxdomain(12) == lead's published 9  — mine=9
- `[PASS]` my 𝓜_12 point count == lead's 8,281  — mine=8,281
- `[PASS]` lead's D=12 argmax members all attain my max  — mine=[438939648]
| 12 | 9 | 8,281 | 9 | 8,281 | [438939648] |
- `[PASS]` my maxdomain(14) == lead's published 9  — mine=9
- `[PASS]` my 𝓜_14 point count == lead's 14,400  — mine=14,400
- `[PASS]` lead's D=14 argmax members all attain my max  — mine=[438939648, 231928233984]
| 14 | 9 | 14,400 | 9 | 14,400 | [438939648, 231928233984] |
- `[PASS]` my maxdomain(15) == lead's published 10  — mine=10
- `[PASS]` my 𝓜_15 point count == lead's 18,496  — mine=18,496
- `[PASS]` lead's D=15 argmax members all attain my max  — mine=[4996238671872]
| 15 | 10 | 18,496 | 10 | 18,496 | [4996238671872] |
- `[PASS]` my maxdomain(16) == lead's published 10  — mine=10
- `[PASS]` my 𝓜_16 point count == lead's 23,409  — mine=23,409
- `[PASS]` lead's D=16 argmax members all attain my max  — mine=[4996238671872]
| 16 | 10 | 23,409 | 10 | 23,409 | [4996238671872] |
- `[PASS]` my maxdomain(18) == lead's published 10  — mine=10
- `[PASS]` my 𝓜_18 point count == lead's 36,100  — mine=36,100
- `[PASS]` lead's D=18 argmax members all attain my max  — mine=[4996238671872, 937638166841712]
| 18 | 10 | 36,100 | 10 | 36,100 | [4996238671872, 937638166841712] |
- `[PASS]` my maxdomain(20) == lead's published 10  — mine=10
- `[PASS]` my 𝓜_20 point count == lead's 53,361  — mine=53,361
- `[PASS]` lead's D=20 argmax members all attain my max  — mine=[4996238671872, 937638166841712]
| 20 | 10 | 53,361 | 10 | 53,361 | [4996238671872, 937638166841712] |
- `[PASS]` my maxdomain(22) == lead's published 10  — mine=10
- `[PASS]` my 𝓜_22 point count == lead's 76,176  — mine=76,176
- `[PASS]` lead's D=22 argmax members all attain my max  — mine=[4996238671872, 937638166841712]
| 22 | 10 | 76,176 | 10 | 76,176 | [4996238671872, 937638166841712] |
- `[PASS]` **maxdomain(22) == 10 — the D=22 milestone** (𝓜₂₂ ⊆ {m ≤ 9²²}, so any published value ≠ 10 means someone's method is buggy)

`src/lattice_search.py` (agent A) not yet published at run time; the comparison above is against the lead's independent milestones (`results/lead_milestones.md`). **Whatever agent A publishes for maxdomain(22) must be exactly 10** — my value-domain scan (𝓜₂₂ ⊆ {7-smooth ≤ 9²²}) and exhaustive 𝓜₂₂ scan both give 10.

## 2. PREIMAGE ATTACK on the P = 10 frontier

For every 7-smooth m with P(m) ≥ 10 and len(m) ≤ 22 (attack 1), does there exist a 7-smooth m′ = 2^a·3^b·5^c·7^d with len(m′) = len23(a,b)+c+d ≤ 30 and Π(m′) = m? Any hit gives n = prime_digit_expansion(a,b,c,d) with P(n) = 2 + P(m) ≥ 12.
- enumerated **246,016** exponent tuples with len23(a,b)+c+d ≤ 30 in 0.2s; depth profile of P(Π(m′)) over all m′: {0: 239292, 1: 6134, 2: 378, 3: 142, 4: 41, 5: 12, 6: 8, 7: 5, 8: 2, 9: 2}
- `[PASS]` attack-2 self-test: m′ = 4996238671872 = 2^19·3^4·7^6 is enumerated and Π(m′) = 438939648 lands in the P ≥ 9 frontier
- `[PASS]` end-to-end pipeline test: prime_digit_expansion(19,4,0,6) has naive P = 11
- **hits with P(Π(m′)) ≥ 10: 0** (expected 0) — of which 0 also satisfy the literal len(m) ≤ 22 frontier-set condition
- closest misses — hits against the P ≥ 9 frontier: **2**
- no preimage of any P ≥ 10 7-smooth exists with len ≤ 30 → **no persistence-12 number is reachable from the known frontier within 30-digit preimages**

Closest-miss examples (m′ → Π(m′), P(Π(m′))):
- 2^19·3^4·5^0·7^6 = 4996238671872 → Π = 438939648 (P = 9)
- 2^4·3^20·5^0·7^5 = 937638166841712 → Π = 438939648 (P = 9)
- full list → results/redteam_preimage_hits.csv

## 3. MONTE CARLO — 2,000,000 rejection-sampled (a,b,c,d) with len ≤ 600 + 200,000 length-stratified supplement
- `[PASS]` len23 flat == library on the full [0,1800]×[0,1200] table (2,163,001 cells — the DP the lattice search rests on)  — (1s to build library table)
- `[PASS]` len23 certificates on 67 cells across the full range  — bad=[]
- len23 cross-validation: 1s
- sampled **2,200,000** points in 4s (48,320,837 proposals, acceptance 4.6%); **max P seen = 9**
- **P-histogram (all 2.2M samples):** P=0: 609, P=1: 2,196,971, P=2: 1,913, P=3: 354, P=4: 110, P=5: 28, P=6: 8, P=7: 5, P=8: 1, P=9: 1
- `[PASS]` naive re-verification of all P ≥ 9 MC samples (1) + 2000 random P = 8 samples  — bad=[]

### Empirical P(digit-length) curve (decimal digit count of m; full curve → results/redteam_mc_curve.csv)

| digits | n | n_plain | n_strat | mean P | max P |
|---|---|---|---|---|---|
| 1 | 609 | 0 | 609 | 0.000 | 0 |
| 2 | 561 | 0 | 561 | 1.631 | 3 |
| 3 | 622 | 0 | 622 | 1.887 | 4 |
| 4 | 647 | 0 | 647 | 1.595 | 5 |
| 5 | 651 | 0 | 651 | 1.593 | 6 |
| 6 | 639 | 0 | 639 | 1.408 | 5 |
| 7 | 631 | 0 | 631 | 1.387 | 8 |
| 8 | 671 | 0 | 671 | 1.218 | 5 |
| 9 | 630 | 1 | 629 | 1.194 | 6 |
| 10 | 599 | 0 | 599 | 1.184 | 6 |
| 11 | 600 | 1 | 599 | 1.137 | 4 |
| 12 | 631 | 0 | 631 | 1.133 | 9 |
| 13 | 626 | 0 | 626 | 1.112 | 3 |
| 14 | 631 | 0 | 631 | 1.068 | 4 |
| 15 | 580 | 1 | 579 | 1.064 | 3 |
| 16 | 640 | 1 | 639 | 1.084 | 7 |
| 17 | 689 | 0 | 689 | 1.062 | 2 |
| 18 | 670 | 1 | 669 | 1.040 | 2 |
| 19 | 656 | 1 | 655 | 1.030 | 2 |
| 20 | 641 | 1 | 640 | 1.017 | 2 |
| 21 | 649 | 0 | 649 | 1.017 | 2 |
| 22 | 680 | 2 | 678 | 1.019 | 2 |
| 23 | 626 | 1 | 625 | 1.019 | 2 |
| 24 | 619 | 2 | 617 | 1.018 | 2 |
| 25 | 613 | 0 | 613 | 1.010 | 2 |
| 26 | 641 | 2 | 639 | 1.017 | 2 |
| 27 | 633 | 2 | 631 | 1.008 | 2 |
| 28 | 614 | 0 | 614 | 1.008 | 2 |
| 29 | 639 | 0 | 639 | 1.006 | 2 |
| 30 | 638 | 4 | 634 | 1.011 | 2 |
| 35 | 606 | 5 | 601 | 1.000 | 1 |
| 40 | 638 | 7 | 631 | 1.002 | 2 |
| 50 | 618 | 16 | 602 | 1.000 | 1 |
| 60 | 636 | 13 | 623 | 1.000 | 1 |
| 80 | 668 | 55 | 613 | 1.000 | 1 |
| 100 | 729 | 121 | 608 | 1.000 | 1 |
| 150 | 980 | 419 | 561 | 1.000 | 1 |
| 200 | 1,508 | 977 | 531 | 1.000 | 1 |
| 300 | 3,553 | 3,177 | 376 | 1.000 | 1 |
| 400 | 7,946 | 7,803 | 143 | 1.000 | 1 |
| 500 | 9,141 | 9,121 | 20 | 1.000 | 1 |

The zero-wall is visible: m with ≥ ~25 digits almost always contains a 0 digit, so P(m) = 1. High persistence lives exclusively at short lengths — which attack 1 and the 𝓜_D scans cover exhaustively.

## 4. BRUTE SANITY — DP-array scan to 10⁸ (test_core.test_brute_1e7 pattern)
- scanned [0, 10⁸) in 9s (~11.3M n/s): **max P = 9, first attained at 26888999**
- `[PASS]` max P below 10⁸ == 9, first attained at 26888999 (s₉; s₁₀ = 3778888999 > 10⁸ so nothing higher can appear)
- P-level counts below 10⁸: P=0: 10, P=1: 51,573,356, P=2: 35,004,331, P=3: 7,168,942, P=4: 3,616,739, P=5: 1,809,689, P=6: 364,820, P=7: 326,732, P=8: 127,933, P=9: 7,448
- `[PASS]` 5000 random n < 10⁸: persistence() == DP value (cross-validates the F2 zero-shortcut against the shortcut-free DP at scale)  — bad=[]
- `[PASS]` record anchors in DP: P(26888999) = 9, P(2677889) = 8, Π(26888999) = 4478976

## Bug reports (persistence.py is read-only — reported, not patched)

### BUG C-1: `len_of_smooth` crashes when exactly one of a, b is 0

Repro: `len_of_smooth(0,5,1,1) raises TypeError: 'NoneType' object is not subscriptable`. Root cause: the default-argument expression `len23_table(a, b) if a and b else ([[0]] if a == 0 and b == 0 else None)` evaluates to `None` when a == 0 XOR b == 0 (e.g. m = 3⁵·5·7 or m = 2⁵·7), and the function then subscripts `None`. Severity: crash (not silent wrong math), but it fires on the a = 0 and b = 0 axes of the lattice — exactly where an exhaustive 𝓜_D searcher walks. Workaround used here: index `len23_table` directly (len = c + d + t23[a][b]). Suggested fix for the lead:
```python
if t23 is None:
    t23 = len23_table(a, b)  # the table itself handles a==0 or b==0 correctly
```

### Spec errata (no action needed, recorded for the record)

- The brief says the 7-smooth heap domain contains "~10^4 numbers"; the actual count of 7-smooth ≤ 9²² is 118,129 (§1). No consequence.
- The brief says 277777788888899 is "> 9²²"; in fact 277777788888899 ≈ 2.78×10¹⁴ < 9²² ≈ 9.85×10²⁰. It is absent from the heap set because it is **not 7-smooth** (that is exactly why it can carry P = 11 while every 7-smooth ≤ 9²² has P ≤ 10). Tested separately as required.

## Verdict

**CONJECTURE SURVIVES all four attacks.** No 7-smooth ≤ 9²² has P ≥ 11 (max = 10, first at 4996238671872); no 30-digit preimage of any P ≥ 10 frontier member exists (0 hits vs 0 expected, closest misses are the known P = 9 family); 2.2M Monte Carlo samples up to 600-digit m never exceeded the known frontier; the 10⁸ DP scan confirms max P = 9 below 10⁸ with s₁₀ = 3778888999 safely above. One real bug found (len_of_smooth axes crash) plus two spec errata — see above.

*Run completed in 17s; redteam_search.py by subagent C.*
