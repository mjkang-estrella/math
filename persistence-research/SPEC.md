# SPEC — Attack on the Multiplicative Persistence Conjecture

**Hypothesis under attack (the "11-step conjecture"):** No positive integer has
multiplicative persistence ≥ 12 in base 10, i.e. every n reaches a single digit
in at most 11 iterations of "multiply the digits". Record: 277777788888899 has
persistence exactly 11 and is the smallest such number (OEIS A003001). Nobody has
ever found a 12-step number, and nobody has proved 12 is impossible.

**Definitions (base 10):**
- `Pi(n)` := product of the decimal digits of n (`Pi(0)=0`).
- `P(n)` := persistence = number of iterations of Pi to reach a single digit;
  `P(n) = 0` for `n < 10`; `P(n) = 1 + P(Pi(n))` for `n >= 10`.

## Master reduction (proved in notes/theory.md, Theorem 1)

> **A number with persistence ≥ 12 exists  ⟺  a 7-smooth number with persistence ≥ 11 exists.**

(7-smooth = of the form `2^a·3^b·5^c·7^d`. Forward: `Pi(n)` is always 7-smooth
and `P(Pi(n)) = P(n) - 1`. Backward: the number spelled `2…23…35…57…7`
(a `2`s, b `3`s, c `5`s, d `7`s) has digit product exactly `2^a·3^b·5^c·7^d`.)

**So the whole conjecture = "every 7-smooth number has P ≤ 10".** The search
space is the 4-D lattice (a,b,c,d), not all integers.

## Length-domain completeness (Theorem 3 prerequisite)

Let `len(m)` := minimum number of digits (1-9) whose product is m. Then:
- `len(2^a·3^b·5^c·7^d) = len23(a,b) + c + d` where `len23(a,b)` is the minimum
  number of digits from {2,3,4,6,8,9} with product `2^a·3^b` (computable exactly
  by DP; see `src/persistence.py:len23_table`). Proof sketch: digits divisible by
  5 are exactly {5}, by 7 exactly {7}, and these contribute no 2s/3s, so the
  5-part, 7-part and 2/3-part decompose.
- **Completeness:** if n < 10^D has P(n) ≥ 12 then m := Pi(n) satisfies
  `m = 2^a·3^b·5^c·7^d`, `len(m) ≤ D` (m is literally a product of n's ≤ D
  digits), and `P(m) ≥ 11`.
- **Therefore:** if every m in `𝓜_D := {(a,b,c,d) : len23(a,b)+c+d ≤ D}` has
  `P(m) ≤ 10`, then **no n < 10^D has persistence ≥ 12**. This is the theorem
  the lattice searcher proves. Any `P(m) ≥ 11` found in 𝓜_D is a *discovery*
  (it constructs a persistence-12 number via the prime-digit expansion).

## Shared library

`src/persistence.py` — **read-only for subagents.** If you find a bug, report it;
do not silently patch it. Exact-persistence shortcuts used there (each provably
equivalent): `P(n)=0` for n<10; `'0' in str(n)` ⇒ `P(n)=1` (next iterate is 0,
a single digit). F5: max persistence below 10^7 is 8 (brute-force verified in
`src/test_core.py`), so `P(x) ≤ 8` for `10 ≤ x < 10^7` — safe pruning filter.

## Layout

```
SPEC.md                  this file
notes/theory.md          theorems + proofs (lead agent)
notes/literature.md      verified citations & current status (agent D)
src/persistence.py       shared core (read-only)
src/test_core.py         unit + brute-force cross-validation (run: python3 src/test_core.py)
src/lattice_search.py    agent A: exhaustive 𝓜_D search
src/zero_free_scan.py    agent B: zero-digit-free 7-smooth numbers
src/redteam_search.py    agent C: independent + adversarial searches
results/                 agents write their <name>_results.md here
```

## Ground rules for all subagents

1. Read SPEC.md and src/persistence.py first. Import the core; don't fork the math.
2. Every high-persistence candidate must be re-verified with a **naive chain**
   (no shortcuts) before being reported.
3. Correctness gates come before scale. Never report an unvalidated number.
4. Write results to `results/<yourname>_results.md` (what was run, D reached,
   wall time, max persistence seen, artifacts). Print a one-paragraph summary.
5. Machine: 32 cores, Python 3.14, **no gcc, no pip/gmpy2** — pure stdlib Python.
   Use multiprocessing. Save incrementally; make long runs resumable.
