
## 2. My checker and its run on the 121 certificates (task 2)

`check_sym_F.py` — stdlib only, no import of generator/projection/legacy code. It checks: meta (format, `unordered`, `scope=full`, distinct positive coefficients, `qmin > v2(K)`, `pin2 ⇒ qmin ≥ t0+3`, `pin_digits ≤ min(3,qmin)`, root = all-zero mod 1); canonical sorted residues; node/parent/modulus headers; unique ids; no cycles; reachability; child ⊂ `Lift(parent)` (weak compositions, own code); every non-explicit lift killed by a listed prime, re-derived from scratch (primality by trial division, orders by factoring `p−1`, signatures, sumset, pin cosets); size leaves by an own DFS over strictly decreasing positions; a brute box (`L ≤ 11`, every injective placement) that must agree with the leaf-declared solutions. Every kill is also classified by the *weakest* pin variant that still kills it (`plain` < `p2` < `tail` < `both`) so that the contribution of the new kill types can be counted.

Run: `run_all.sh files121.txt logs/all 11` (16 parallel processes, ≈ 25 min wall on a loaded machine). Per-certificate JSON: `logs/all/*.json`; aggregate: `summary_F.json`.

| item | count |
|---|---|
| certificates checked | 121 (dim 6: 89, dim 7: 32) |
| **PASS** | **121** |
| FAIL | 0 |
| tree nodes (explicit) | 62 676 |
| refinements (lifts) enumerated and each either child or killed | 112 873 032 |
| killed lifts (all re-verified) | 112 810 477 |
| leaves | 198 = 114 prime leaves + 84 size leaves |
| declared / found solutions (all size leaves) | 0 / 0 |
| brute-box points (`L ≤ 11`) / smooth hits | 360 600 / 0 |

Pass/fail per kill type (instances of verified kills; "unique" = distinct (prime, signature, reduced class) cache entries actually evaluated):

| kill type (weakest sufficient variant) | instances verified | unique | PASS | FAIL |
|---|---|---|---|---|
| aligned prime, plain (no pin needed) | 105 617 519 | 51 011 716 | all | 0 |
| aligned prime + **mod-8 pin** (`p2`) needed | 4 222 263 | 2 474 017 | all | 0 |
| aligned prime + **decimal-tail coset** needed | 2 970 695 | 880 834 | all | 0 |
| **sumset** (unaligned prime), needs tail coset | 114 (prime leaves, in 24 of the 26 `decimal5_high` certs) | 114 | all | 0 |
| sumset without any pin | 0 occurrences | – | – | – |
| multiset lifts (partition/completeness) | 112 873 032 lifts | – | all | 0 |
| size leaves (empty by size) | 84 | – | all | 0 |

Observations. (i) The sumset kill occurs *only* as the final prime leaf (114 instances, never as an internal "rest" kill), and in every one of them the kill needs the tail coset (the plain sumset does not kill). (ii) For the `broad_pin2` stage (37 certs) the new ingredient is the mod-8 pin (1.1 M kills need it); for `decimal_full`, `decimal5_high`, `decimal_pilot` the tail coset (3.0 M kills). (iii) All 121 certificates have `K` odd (`t0 = 0`) and `qmin = 3`, so pin2 (`qmin ≥ 3`) is valid, `k = 3 ≤ qmin`, and the "divide by `2^{t0}`" subtlety is vacuous for the certificates themselves; it is exercised by the positive controls (t0 ∈ {0,1,3}, §3).
