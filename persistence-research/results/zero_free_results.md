# Zero-free 7-smooth numbers (Agent B)

Run 2026-10-19 11:19:48, wall 1 s total
(scan phase 0 s), Python 3.14.7, 32 workers,
pure stdlib + `src/persistence.py`.

## Headline

**Z = 140** -- the largest decimal digit-length of any zero-free 7-smooth number
found by any scan below.  It is attained by

    31262221321885653647626425815737111943458241183262682285162767533715254994149452428386848427865279586287233185834769954797571297422117699584
    = 2^25 * 3^227 * 5^0 * 7^28
    exponent tuple (a,b,c,d) = (25,227,0,28)

So, empirically, the conjecture reduces to: *every 7-smooth number with more than 140 digits contains the digit 0* (Theorem 4), pending the finite part for len(m) <= 140 (lattice searcher).

Largest zero-free pure powers (complete lists in `zero_free_powers.txt`):

| prime | max 0-free exponent | digit length | the number |
|---|---|---|---|
| 2 | 86 | 26 | `77371252455336267181195264` |
| 3 | 68 | 33 | `278128389443693511257285776231761` |
| 5 | 58 | 41 | `34694469519536141888238489627838134765625` |
| 7 | 35 | 30 | `378818692265664781682717625943` |

(matches the literature-known largest zero-free power of 2, 2^86)

## Method

1. **Pure powers**: incremental `m *= p`, `s = str(m)`, `'0' in s` test, for
   2^a (a <= 200000), 3^b (b <= 127000), 5^c (c <= 86000),
   7^d (d <= 71200) -- max digit lengths
   60206/60595/60112/60171.
   Measured str() cost t(us) = 8.040e-04 * digits^1.438 (subquadratic,
   CPython 3.14.7); projected 1194 core-s,
   sharded into cost-balanced exponent ranges across 32 workers
   (484,204 string tests).
2. **Full lattice to 500 digits**: every 2^a*3^b*5^c*7^d < 10^500 was
   classified.  **Trailing-zero lemma** (Gate 3/4 verified): if a >= 1 and
   c >= 1 then 10 | m, so m ends in '0' -- about
   3.04e+10 of the ~3.07e+10 naive lattice points
   (99.2%) are pruned with no string test.  The remaining
   246,844,322 points are exactly the two faces {c=0} = lattice (2,3,7) and
   {a=0} = lattice (3,5,7), walked depth-first with incremental multiplies,
   sharded by the largest exponent (a, resp. b) across 32 workers.
   This SUBSUMES all pairs <= 500 digits, all triples <= 500 digits and the
   quadruple <= 500 digits (the brief's budgets were pairs 500,
   triples/quad 250 -- all exceeded).
3. **Cross-checks** (Gate 5): six standalone pair scans (<= 500 digits) and two
   standalone interior-triple scans (<= 250 digits; 2,753,526 further
   string tests) were run independently and compared, as sets, against the
   corresponding slices of the face scans.  All equal.

## Sanity gates (all printed before the run; source: `run_gates()`)

- GATE 1: 2^0..2^9 zero-free; 2^10 = 1024 contains '0'.
- GATE 2: zero-test agrees with a naive divmod digit scan on 1000 random ints.
- GATE 3: pruned == unpruned == brute-force enumeration of all 7-smooth < 10^6.
- GATE 4: 500 random exponent tuples: a >= 1 and c >= 1 always gives '0' in str(m).
- GATE 5: every standalone pair/triple scan equals its extraction from the faces.
- Every recorded hit is regenerated from (a,b,c,d); len(str(m)) is asserted.

## Zero-free 7-smooth numbers by digit-length bucket

| digit length | count |
|---|---|
| 1-9 | 992 |
| 10-19 | 3306 |
| 20-29 | 3274 |
| 30-39 | 2307 |
| 40-49 | 1375 |
| 50-59 | 736 |
| 60-69 | 358 |
| 70-79 | 141 |
| 80-89 | 82 |
| 90-99 | 25 |
| 100-109 | 11 |
| 110-119 | 3 |
| 120-129 | 3 |
| 130-139 | 1 |
| 140-149 | 1 |

Total distinct zero-free 7-smooth numbers found: **12,615**
(484,204 pure-power tests, 249,597,848 lattice tests).

## Coverage (what was exhaustively checked)

- **[1, 500] digits, exhaustive over the FULL 4-prime lattice**: no zero-free
  7-smooth number with digit-length in [141, 500] exists.  Every
  2^a*3^b*5^c*7^d < 10^500 was classified (246,844,322 string tests plus the
  lemma-pruned remainder, correctness gated as above).
- **Pure powers**: no zero-free 2^a for a <= 200000 (60206 digits),
  3^b for b <= 127000 (60595 digits), 5^c for c <= 86000
  (60112 digits), 7^d for d <= 71200 (60171 digits) -- i.e. no
  zero-free pure power with digit-length in [141, ~60,000].
- **Two-prime products** are covered to 500 digits (inside the lattice scan);
  **three-prime products and the quadruple** likewise to 500 digits.
- Beyond those ranges: not covered empirically (handled by theory / the
  lattice searcher's completeness theorem).

## Artifacts

- `results/zero_free_results.md` -- this file
- `results/zero_free_list.txt` -- all zero-free 7-smooth numbers with >= 40
  digits: `<decimal> (a,b,c,d)` per line
- `results/zero_free_powers.txt` -- every 0-free pure power with digit length
- `results/zero_free_hits.jsonl` -- raw hits per task (resumable)
- `src/zero_free_scan.py` -- the scanner (gates, benchmark, scans, report)
